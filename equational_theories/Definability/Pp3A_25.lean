import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_pxx_pxy_Equation4554 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4554 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X0
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
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
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq164 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq86 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq86
    | exact resolve eq86 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq177 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X4) X0) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 x x X0 X4
       have i₂ := eq16 x x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 X3 X4 (M.op x X0)
       have i₂ := eq16 X4 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X0 X1 X2 x
       have i₂ := eq16 X3 X4 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op X3 (M.op X4 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 X3 (M.op X4 X0) x
       have i₂ := eq16 (M.op (M.op X4 X0) x) X4 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq177 X2 x
       have i₂ := eq177 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq190 eq178
    | exact resolve eq178 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq263 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op x y) x) y) := by
    intro X1
    first
    | (have i₁ := eq177 X1 (M.op x x)
       have i₂ := eq183 y x
       grind)
    | exact superpose eq183 eq177
    | exact resolve eq177 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq178 x (M.op X1 x)
       have i₂ := eq183 sF3 X1
       grind)
    | exact superpose eq183 eq178
    | exact resolve eq178 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X1
    first
    | exact superpose eq184 eq178
    | exact resolve eq178 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq858 : (M.op x y) = (k x y) ∨ x = (M.op x x) := by
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
  have eq864 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq870 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq858
       grind)
    | exact superpose eq858 eq41
    | exact resolve eq41 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq1110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1109
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1109
    | exact resolve eq1109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1110
    | exact resolve eq1110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1112 eq864
    | exact resolve eq864 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq1112
  have eq1208 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1201
       have r₂ := eq27
       grind)
    | exact resolve eq1201 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1216 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1208 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1208
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1208
       grind)
    | exact resolve eq13 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3769 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq1216 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq3770 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1208 eq3769
    | exact resolve eq3769 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208 eq3769
  have eq3773 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3770 eq142
    | exact resolve eq142 eq3770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq3770
  have eq3776 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq3773
    | exact resolve eq3773 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3773
  have eq3779 : x = (M.op x x) := by
    first
    | (have j1 := eq870 x
       grind)
    | (have r₁ := eq3776
       have r₂ := eq870 x
       grind)
    | exact resolve eq3776 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq3784 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq183 X0 x
       have i₂ := eq3779
       grind)
    | exact superpose eq3779 eq183
    | exact resolve eq183 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3790 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq179 x X0 x
       have i₂ := eq3779
       grind)
    | exact superpose eq3779 eq179
    | exact resolve eq179 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3794 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3790 X0
       have i₂ := eq3779
       grind)
    | exact superpose eq3779 eq3790
    | exact resolve eq3790 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790
  have eq3797 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3794 x
       have i₂ := eq3784 (M.op x x)
       grind)
    | (have i₁ := eq3794 y
       have i₂ := eq3784 x
       grind)
    | exact superpose eq3784 eq3794
    | (have j0 := eq3794 y
       grind)
    | exact resolve eq3794 eq3784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3784 eq3794
  have eq3801 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3797 eq263
    | exact resolve eq263 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq3802 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op x (σ y)) := by
    intro X0
    first
    | exact superpose eq3797 eq264
    | exact resolve eq264 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq3807 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq3797 eq183
    | exact resolve eq183 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq3797
  have eq3818 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3801 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3801
    | (have j0 := eq3801 X0
       grind)
    | exact resolve eq3801 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3801
  have eq3841 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2 x
       have i₂ := eq3807 X2
       grind)
    | exact superpose eq3807 eq16
    | exact resolve eq16 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3920 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq3818 eq16
    | exact resolve eq16 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3921 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq3818 eq28
    | (have j0 := eq28 X0 x
       grind)
    | exact resolve eq28 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3923 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq3818 eq179
    | exact resolve eq179 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq3935 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq3818 eq177
    | exact resolve eq177 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3940 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op x y) (σ y)) := by
    intro X0
    first
    | exact superpose eq3818 eq178
    | exact resolve eq178 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq3943 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq3818 eq3935
    | exact resolve eq3935 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3935
  have eq4069 : ∀ X1 : G, (M.op (M.op X1 (M.op x y)) (σ y)) = (M.op x (σ y)) := by
    intro X1
    first
    | exact superpose eq3802 eq222
    | exact resolve eq222 eq3802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq3802
  have eq4125 : (M.op x (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq3818 eq4069
    | exact resolve eq4069 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4069
  have eq4246 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0 X0
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq16
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4249 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op y y) y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y
       have i₂ := eq188 y
       grind)
    | exact superpose eq188 eq177
    | exact resolve eq177 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq4275 : x = (k (M.op x x) x) := by
    first
    | (have i₁ := eq3807 (M.op x x)
       have i₂ := eq188 x
       grind)
    | exact superpose eq188 eq3807
    | exact resolve eq3807 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3807
  have eq4289 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq3818 (M.op sF0 sF0)
       have i₂ := eq188 sF0
       grind)
    | exact superpose eq188 eq3818
    | exact resolve eq3818 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4332 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3818 eq4289
    | exact resolve eq4289 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4289
  have eq4345 : x = (k x x) := by
    first
    | (have i₁ := eq4275
       have i₂ := eq3779
       grind)
    | exact superpose eq3779 eq4275
    | exact resolve eq4275 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3779 eq4275
  have eq4360 : (M.op x y) = (k (M.op y y) y) := by
    first
    | exact superpose eq3818 eq4249
    | exact resolve eq4249 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3818 eq4249
  have eq4362 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq4246 X0 x x
       have i₂ := eq3841 x x X0
       grind)
    | exact superpose eq3841 eq4246
    | exact resolve eq4246 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4246
  have eq5250 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4332 eq42
    | exact resolve eq42 eq4332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq4332
  have eq5253 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq5250
    | exact resolve eq5250 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5250
  have eq5256 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4345
       grind)
    | exact superpose eq4345 eq40
    | exact resolve eq40 eq4345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4345
  have eq5259 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq5256
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5256
    | exact resolve eq5256 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5256
  have eq5264 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5253 eq870
    | (have j0 := eq870 (σ (M.op x y))
       grind)
    | (have r₁ := eq870 (σ (M.op x y))
       have r₂ := eq5253
       grind)
    | exact resolve eq870 eq5253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5253
  have eq5265 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5264
  have eq5272 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5259 eq870
    | (have j0 := eq870 (σ x)
       grind)
    | (have r₁ := eq870 (σ x)
       have r₂ := eq5259
       grind)
    | exact resolve eq870 eq5259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq5259
  have eq5273 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5272
  have eq5941 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ (M.op x y)))) = (M.op X2 (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5265 eq185
    | exact resolve eq185 eq5265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5946 : ∀ X2 : G, (M.op X2 (σ (M.op x y))) = (M.op x (σ (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq5941 x x X2
       have i₂ := eq3841 x x sF1
       grind)
    | exact superpose eq3841 eq5941
    | exact resolve eq5941 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5941
  have eq5978 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq5273 eq16
    | exact resolve eq16 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5981 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (σ x) (σ x)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq5273 eq181
    | exact resolve eq181 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq5984 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X2 (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq5273 eq185
    | exact resolve eq185 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq5989 : ∀ X2 : G, (M.op X2 (σ x)) = (M.op x (σ x)) := by
    intro X2
    first
    | (have i₁ := eq5984 x x X2
       have i₂ := eq3841 x x sF2
       grind)
    | exact superpose eq3841 eq5984
    | exact resolve eq5984 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5984
  have eq5992 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ x) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq5273 eq5981
    | exact resolve eq5981 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5981
  have eq5995 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq5273 eq5978
    | exact resolve eq5978 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273 eq5978
  have eq5999 : ∀ X2 : G, (M.op (M.op x y) X2) = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq5992 x x X2
       have i₂ := eq3920 x x X2
       grind)
    | exact superpose eq3920 eq5992
    | exact resolve eq5992 eq3920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920 eq5992
  have eq6002 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq5995 x x
       have i₂ := eq3841 x x sF2
       grind)
    | exact superpose eq3841 eq5995
    | exact resolve eq5995 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5995
  have eq6036 : (σ (M.op x y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq4360
       grind)
    | exact superpose eq4360 eq41
    | exact resolve eq41 eq4360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6037 : (σ (M.op x y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | exact superpose eq20 eq6036
    | exact resolve eq6036 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6036
  have eq6451 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq5946 eq5265
    | exact resolve eq5265 eq5946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5265
  have eq6492 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq6451 eq5946
    | exact resolve eq5946 eq6451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6885 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq5989 eq6002
    | exact resolve eq6002 eq5989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989 eq6002
  have eq6977 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) X0) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6885 eq186
    | exact resolve eq186 eq6885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq7008 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq6885 eq278
    | exact resolve eq278 eq6885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq6885
  have eq7017 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq7008
    | (have j0 := eq7008 X0
       grind)
    | exact resolve eq7008 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq7008
  have eq7027 : ∀ X0 X3 : G, (M.op (σ x) X0) = (M.op x (M.op X3 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq6977 X0 x x X3
       have i₂ := eq3841 x x (M.op X3 X0)
       grind)
    | exact superpose eq3841 eq6977
    | exact resolve eq6977 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6977
  have eq7042 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq7027 X0 x
       have i₂ := eq3841 x x X0
       grind)
    | exact superpose eq3841 eq7027
    | exact resolve eq7027 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3841 eq7027
  have eq7046 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq5999 eq7042
    | exact resolve eq7042 eq5999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5999 eq7042
  have eq7086 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq7017 eq3940
    | exact resolve eq3940 eq7017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3940
  have eq7088 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq7017 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) x
       have r₂ := eq7017 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq7017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7017
  have eq7123 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7088 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7088
  have eq9735 : (σ (M.op x y)) = (k (σ (k y y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6037
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq6037
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq6037 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6037
  have eq9746 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9735
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq9735
    | exact resolve eq9735 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9735
  have eq9750 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9746
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9746
    | exact resolve eq9746 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9746
  have eq9894 : (k (τ (M.op (σ y) (σ y))) y) = (τ (M.op x (σ y))) := by
    first
    | (have i₁ := eq153 (M.op sF3 sF3)
       have i₂ := eq4362 sF3
       grind)
    | exact superpose eq4362 eq153
    | exact resolve eq153 eq4362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq4362
  have eq9895 : (k (τ (M.op (σ y) (σ y))) y) = (τ (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq4125 eq9894
    | exact resolve eq9894 eq4125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4125 eq9894
  have eq9940 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq7086 eq9895
    | exact resolve eq9895 eq7086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9895
  have eq10826 : (τ (M.op (σ x) (σ y))) = (k (τ (k (σ y) (σ y))) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9940
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq9940
    | (have j1 := eq28 (σ y) x
       grind)
    | exact resolve eq9940 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9940
  have eq10835 : (τ (M.op (σ x) (σ y))) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq116 eq10826
    | exact resolve eq10826 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq10826
  have eq23223 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7123 eq164
    | (have j1 := eq7123 (σ (M.op x y))
       grind)
    | exact resolve eq164 eq7123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq7123
  have eq23231 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) ∨ (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq5946 eq23223
    | exact resolve eq23223 eq5946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23223
  have eq23234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq6451 eq23231
    | exact resolve eq23231 eq6451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6451 eq23231
  have eq23235 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | (have r₁ := eq23234
       have r₂ := eq27
       grind)
    | exact resolve eq23234 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23234
  have eq23238 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq23235 eq3921
    | (have j0 := eq3921 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq3921 eq23235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921 eq23235
  have eq35082 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq23238 eq3923
    | exact resolve eq3923 eq23238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35089 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq23238 eq35082
    | exact resolve eq35082 eq23238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23238 eq35082
  have eq38505 : (k (σ (k y y)) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq10835
       grind)
    | exact superpose eq10835 eq41
    | exact resolve eq41 eq10835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10835
  have eq38519 : (M.op (σ x) (σ y)) = (k (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq38505
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq38505
    | exact resolve eq38505 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38505
  have eq38525 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq38519
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq38519
    | exact resolve eq38519 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq38519
  have eq38528 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq38525
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38525
    | exact resolve eq38525 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38525
  have eq38532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq38528 eq9750
    | exact resolve eq9750 eq38528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9750 eq38528
  have eq38547 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq38532
       have r₂ := eq27
       grind)
    | exact resolve eq38532 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38532
  have eq38600 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq38547 eq3923
    | exact resolve eq3923 eq38547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3923
  have eq38608 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7086 eq38600
    | exact resolve eq38600 eq7086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38600
  have eq38637 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38547 eq38608
    | exact resolve eq38608 eq38547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38547 eq38608
  have eq38691 : (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4360
       have i₂ := eq38637
       grind)
    | exact superpose eq38637 eq4360
    | exact resolve eq4360 eq38637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360
  have eq38701 : (k y y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq188 y
       have i₂ := eq38637
       grind)
    | exact superpose eq38637 eq188
    | exact resolve eq188 eq38637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq38752 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38637 eq38701
    | exact resolve eq38701 eq38637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38637 eq38701
  have eq38777 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38691 eq38752
    | exact resolve eq38752 eq38691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38691 eq38752
  have eq38874 : (τ (σ y)) = (M.op (M.op x y) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38777 eq35089
    | exact resolve eq35089 eq38777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35089 eq38777
  have eq38885 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq38874
    | exact resolve eq38874 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38874
  have eq38929 : y = (M.op x y) ∨ (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3943 eq38885
    | exact resolve eq38885 eq3943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3943 eq38885
  have eq38930 : y = (M.op x y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq38929
  have eq38959 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq38930
    | exact resolve eq38930 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq38930
  have eq38960 : y = (M.op x y) := by grind
  clear eq38959
  have eq38983 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38960
       grind)
    | exact superpose eq38960 eq24
    | exact resolve eq24 eq38960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38960
  have eq39062 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38983 eq20
    | exact resolve eq20 eq38983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq38983
  have eq39117 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op x (σ y)) := by
    intro X0
    first
    | exact superpose eq39062 eq5946
    | exact resolve eq5946 eq39062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5946
  have eq39123 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq39062 eq6492
    | exact resolve eq6492 eq39062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6492
  have eq39179 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op x y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq39117 X0
       have i₂ := eq7046 sF3
       grind)
    | exact superpose eq7046 eq39117
    | exact resolve eq39117 eq7046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7046 eq39117
  have eq39190 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq7086 eq39179
    | exact resolve eq39179 eq7086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7086 eq39179
  have eq39199 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39123 eq39190
    | (have j1 := eq39123 (σ x)
       grind)
    | exact resolve eq39190 eq39123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39123 eq39190
  have eq39206 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq39199 eq27
    | exact resolve eq27 eq39199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq39199
  have eq39332 : False := by grind
  exact eq39332

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_x_pxy_Equation4554 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4554 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op X2 x) X2 X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op x y)) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X3 X4 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x (M.op x x)
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq101 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq97
  have eq102 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq101
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq123
  have eq127 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq126
  have eq216 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq55 X2 x
       have i₂ := eq55 X0 x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X3 : G, (M.op X3 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq55 X3 x
       have i₂ := eq14 X0 X1 y x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq216 eq127
    | exact resolve eq127 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq216
  have eq298 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq61 x x
       have i₂ := eq14 x x x X0
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2 (M.op x x)
       have i₂ := eq61 X2 x
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op x y) x) y) := by
    intro X1
    first
    | (have i₁ := eq55 X1 (M.op x x)
       have i₂ := eq61 y x
       grind)
    | exact superpose eq61 eq55
    | exact resolve eq55 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq306 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq56 x (M.op X1 x)
       have i₂ := eq61 sF3 X1
       grind)
    | exact superpose eq61 eq56
    | exact resolve eq56 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X1
    first
    | exact superpose eq62 eq56
    | exact resolve eq56 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq476 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | exact superpose eq217 eq240
    | exact resolve eq240 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq491 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq45
    | exact resolve eq45 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq512 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | exact superpose eq62 eq491
    | exact resolve eq491 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq491
  have eq513 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq512
       have i₂ := eq61 (M.op x x) x
       grind)
    | exact superpose eq61 eq512
    | exact resolve eq512 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq709 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) x) y)) := by
    first
    | exact superpose eq305 eq240
    | exact resolve eq240 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq305
  have eq803 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X2 (M.op X3 (σ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X1 (σ X0) (σ X0) X2 X3
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq63
    | exact resolve eq63 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq927 : (M.op (M.op (M.op x y) x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq306 eq320
    | exact resolve eq320 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq320
  have eq963 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq54 X3 X4 X0 X2 (M.op x x)
       have i₂ := eq61 X0 x
       grind)
    | exact superpose eq61 eq54
    | exact resolve eq54 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3819 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op (M.op x y) x) y))) := by
    first
    | exact superpose eq709 eq45
    | exact resolve eq45 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq3824 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq3819
       have i₂ := eq476 (M.op (M.op sF0 x) y) (M.op sF0 x)
       grind)
    | exact superpose eq476 eq3819
    | exact resolve eq3819 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819
  have eq10920 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op (M.op y y) (M.op y y)))) = (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq803 (M.op y y) X0 X1 X2
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq803
    | exact resolve eq803 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq803
  have eq11160 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10920 X0 X1 X2
       have i₂ := eq476 (M.op y y) y
       grind)
    | exact superpose eq476 eq10920
    | exact resolve eq10920 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq10920
  have eq50873 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3824
       have i₂ := eq302 (M.op sF1 sF1) sF1 sF1
       grind)
    | exact superpose eq302 eq3824
    | exact resolve eq3824 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3824
  have eq50965 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq302 eq50873
    | exact resolve eq50873 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq50873
  have eq59408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ x) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq59416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq59408
    | exact resolve eq59408 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59408
  have eq59421 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq59416
       have r₂ := eq28
       grind)
    | exact resolve eq59416 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59416
  have eq59425 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq59421 eq76
    | exact resolve eq76 eq59421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59421
  have eq59511 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq59425
    | exact resolve eq59425 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59425
  have eq59512 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59511
  have eq59524 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq298 x
       have i₂ := eq59512
       grind)
    | exact superpose eq59512 eq298
    | exact resolve eq298 eq59512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq59527 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq61 X0 x
       have i₂ := eq59512
       grind)
    | exact superpose eq59512 eq61
    | exact resolve eq61 eq59512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq60040 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq59524
       have i₂ := eq59527 sF0
       grind)
    | exact superpose eq59527 eq59524
    | exact resolve eq59524 eq59527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59524 eq59527
  have eq60235 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq60040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60040
  have eq62457 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq59512
       have i₂ := eq60235 X0
       grind)
    | (have i₁ := eq59512
       have i₂ := eq60235 x
       grind)
    | exact superpose eq60235 eq59512
    | exact resolve eq59512 eq60235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59512 eq60235
  have eq62710 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq62457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62457
  have eq63016 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq513
       have i₂ := eq62710 sF0
       grind)
    | exact superpose eq62710 eq513
    | exact resolve eq513 eq62710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq63020 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq709
       have i₂ := eq62710 sF0
       grind)
    | exact superpose eq62710 eq709
    | exact resolve eq709 eq62710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq62710
  have eq63058 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63020
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq63020
    | exact resolve eq63020 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63020
  have eq63060 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63016
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq63016
    | exact resolve eq63016 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63016
  have eq63138 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq63058
    | exact resolve eq63058 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63058
  have eq63162 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63060 eq927
    | exact resolve eq927 eq63060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq63060
  have eq63235 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq63162
    | exact resolve eq63162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63162
  have eq63578 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq63138 eq50965
    | exact resolve eq50965 eq63138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63138
  have eq253713 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (σ y)) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq11160 X0 x x
       have i₂ := eq963 sF3 x x sF3
       grind)
    | exact superpose eq963 eq11160
    | exact resolve eq11160 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963 eq11160
  have eq253714 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq50965 eq253713
    | exact resolve eq253713 eq50965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50965 eq253713
  have eq253722 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63235 eq253714
    | exact resolve eq253714 eq63235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63235 eq253714
  have eq253963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq253722 eq63578
    | exact resolve eq63578 eq253722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63578 eq253722
  have eq254087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq253963
  have eq254142 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq254087
       have r₂ := eq28
       grind)
    | exact resolve eq254087 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254087
  have eq254162 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq254142 eq30
    | exact resolve eq30 eq254142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq254142
  have eq254256 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq254162
    | exact resolve eq254162 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq254162
  have eq254257 : x = y := by grind
  clear eq254256
  have eq254268 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq254257
       grind)
    | exact superpose eq254257 eq19
    | exact resolve eq19 eq254257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq254269 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq254257
       grind)
    | exact superpose eq254257 eq25
    | exact resolve eq25 eq254257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq254257
  have eq254452 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq254269
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq254269
    | exact resolve eq254269 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq254269
  have eq254482 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq254452 eq27
    | exact resolve eq27 eq254452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq254452
  have eq254807 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq254482 eq76
    | exact resolve eq76 eq254482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq254482
  have eq254961 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq254807
       have i₂ := eq254268
       grind)
    | exact superpose eq254268 eq254807
    | exact resolve eq254807 eq254268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254268 eq254807
  have eq254975 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq254961 eq15
    | exact resolve eq15 eq254961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254961
  have eq255052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq254975
    | exact resolve eq254975 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq254975
  have eq255073 : False := by grind
  exact eq255073

/-- `Equation4569`: `x ◇ (y ◇ z) = (w ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_x_pyx_pxy_Equation4569 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4569 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4569.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X2) X2) := by
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
  clear eq47
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X1 y) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X1) X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 x x X1 X4
       have i₂ := eq16 x x X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 X2)) = (M.op (M.op X0 (M.op X1 X2)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X3 X4 X2 (M.op x X2)
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X0 X1 X2 x
       have i₂ := eq16 X3 X4 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op X3 (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 X3 (M.op X4 X1) x
       have i₂ := eq16 (M.op x (M.op X4 X1)) X4 X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq178 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 X0 x
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq178 X2 x
       have i₂ := eq178 X0 x
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x y)) = (M.op X1 (M.op X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 y x
       have i₂ := eq178 X0 x
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x y))) = (M.op (M.op (M.op X0 y) y) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | exact superpose eq192 eq178
    | exact resolve eq178 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X0 (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq192 eq16
    | exact resolve eq16 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ X1 ∨ (M.op x y) = (k (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq193 eq13
    | (have j0 := eq13 (M.op x y) X1
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x (M.op x y))
       have r₂ := eq193 (M.op x (M.op x y)) x
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op X0 (M.op x y))
       have r₂ := eq193 X0 (M.op X0 (M.op x y))
       grind)
    | exact resolve eq13 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq244 : ∀ X0 X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X2
    first
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 X0 (σ x)
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq246 eq179
    | exact resolve eq179 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq425 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x y)) ≠ X1 ∨ (M.op X2 y) = (k (M.op X2 y) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X2 y) X1
       have i₂ := eq197 X0 X1 X2
       grind)
    | (have i₁ := eq13 (M.op x y) X0
       have i₂ := eq197 X0 X1 X2
       grind)
    | exact superpose eq197 eq13
    | (have j0 := eq13 (M.op X2 y) X1
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op X1 (M.op X2 y))
       have r₂ := eq197 (M.op X1 (M.op X2 y)) X1 X2
       grind)
    | (have r₁ := eq13 (M.op X2 y) (M.op X0 (M.op x y))
       have r₂ := eq197 X0 (M.op X0 (M.op x y)) X2
       grind)
    | exact resolve eq13 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) ≠ (M.op X1 (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq244 eq13
    | (have j0 := eq13 (σ y) (M.op X1 (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))
       have r₂ := eq244 X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op x (M.op (σ x) (σ y)))
       have r₂ := eq244 x x
       grind)
    | exact resolve eq13 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq486 : ∀ X1 : G, (σ y) = (k (σ y) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | (have j0 := eq485 x X1
       grind)
    | (have r₁ := eq485 x x
       have r₂ := eq247 x x
       grind)
    | (have r₁ := eq485 x x
       have r₂ := eq247 x x
       grind)
    | exact resolve eq485 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq498 : (σ y) = (k (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq246 eq486
    | exact resolve eq486 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq486
  have eq583 : (τ (σ y)) = (k y (τ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq498 eq107
    | exact resolve eq107 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq498
  have eq594 : y = (k y (τ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq31 eq583
    | exact resolve eq583 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq672 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (k (M.op X0 y) y) ∨ y = (M.op (M.op X0 y) y) ∨ y = (M.op y (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 X0
       have i₂ := eq11 (M.op X0 y) y
       grind)
    | exact superpose eq11 eq178
    | (have j1 := eq11 (M.op X0 y) y
       grind)
    | exact resolve eq178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq720 : ∀ X0 : G, (k (M.op x y) y) = (M.op X0 (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq192 X0
       have i₂ := eq11 sF0 y
       grind)
    | exact superpose eq11 eq192
    | (have j1 := eq11 (M.op x y) y
       grind)
    | exact resolve eq192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 : G, y = (M.op (M.op x y) y) ∨ (k (M.op x y) y) = (M.op X0 (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq192 eq720
    | (have j0 := eq720 X0
       grind)
    | exact resolve eq720 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq731 : ∀ X0 : G, (k (M.op x y) y) = (M.op X0 (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have j0 := eq730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq741 : ∀ X0 X1 : G, y = (M.op (M.op x y) y) ∨ (M.op X1 (M.op x y)) = (k (M.op X0 y) y) ∨ y = (M.op y (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 X0 X1
       have i₂ := eq211 X0
       grind)
    | (have i₁ := eq711 x X1
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq711
    | (have j0 := eq711 X0 X1
       grind)
    | exact resolve eq711 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq779 : ∀ X0 X1 : G, y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ (M.op X1 (M.op x y)) = (k (M.op X0 y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq184 y X0
       grind)
    | exact superpose eq184 eq741
    | (have j0 := eq741 X0 X1
       grind)
    | exact resolve eq741 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq780 : ∀ X0 X1 : G, y = (M.op (M.op x y) y) ∨ (M.op X1 (M.op x y)) = (k (M.op X0 y) y) := by
    intro X0 X1
    first
    | (have j0 := eq779 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq794 : ∀ X0 : G, y = (M.op (M.op x y) y) ∨ (k (M.op x y) y) = (k (M.op X0 y) y) := by
    intro X0
    first
    | exact superpose eq731 eq780
    | exact resolve eq780 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq780
  have eq904 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op X0 y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op x y) y
       have i₂ := eq211 X0
       grind)
    | (have i₁ := eq11 (M.op X0 y) y
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq11
    | (have j0 := eq11 (M.op x y) y
       grind)
    | exact resolve eq11 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : ∀ X0 : G, y = (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op X0 y) y) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq904 X0
       have i₂ := eq184 y X0
       grind)
    | exact superpose eq184 eq904
    | (have j0 := eq904 X0
       grind)
    | exact resolve eq904 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq909 : ∀ X0 : G, y = (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op X0 y) y) := by
    intro X0
    first
    | (have j0 := eq908 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq913 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq794 eq909
    | (have j0 := eq909 x
       grind)
    | exact resolve eq909 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq909
  have eq1224 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1958 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) ≠ X3 ∨ (M.op X4 X2) = (k (M.op X4 X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 (M.op X4 X2) X3
       have i₂ := eq186 X3 X4 X2 X0 X1
       grind)
    | (have i₁ := eq13 (M.op X4 X2) X3
       have i₂ := eq186 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq186 eq13
    | (have j0 := eq13 (M.op X4 X2) X3
       grind)
    | (have r₁ := eq13 (M.op X1 X2) (M.op X3 (M.op X4 X2))
       have r₂ := eq186 (M.op X3 (M.op X4 X2)) X1 X2 X3 X4
       grind)
    | (have r₁ := eq13 (M.op X4 X2) (M.op X0 (M.op X1 X2))
       have r₂ := eq186 X0 X1 X2 (M.op X0 (M.op X1 X2)) X4
       grind)
    | exact resolve eq13 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2310 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X3 (M.op X4 X2)) ∨ (k X2 (M.op X3 (M.op X4 X2))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X2 (M.op X3 (M.op X4 X2))
       have i₂ := eq183 X3 X4 X2 X0 X1
       grind)
    | exact superpose eq183 eq13
    | (have j0 := eq13 X2 (M.op X3 (M.op X4 X2))
       grind)
    | (have r₁ := eq13 (M.op X4 X2) (M.op (M.op X0 (M.op X1 X2)) X2)
       have r₂ := eq183 X0 X1 X2 (M.op (M.op X0 (M.op X1 X2)) X2) X4
       grind)
    | (have r₁ := eq13 X2 (M.op X3 (M.op X4 X2))
       have r₂ := eq183 X3 X4 X2 X3 X4
       grind)
    | exact resolve eq13 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2414 : ∀ X2 X3 X4 : G, (k X2 (M.op X3 (M.op X4 X2))) = X2 := by
    intro X2 X3 X4
    first
    | (have j0 := eq2310 x x X2 X3 X4
       grind)
    | (have r₁ := eq2310 x x X2 X3 X4
       have r₂ := eq186 x x X2 X3 X4
       grind)
    | (have r₁ := eq2310 X3 X4 X2 x x
       have r₂ := eq186 x x X2 X3 X4
       grind)
    | exact resolve eq2310 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq2310
  have eq2948 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2414 X1 x x
       have i₂ := eq16 x x X1 X0
       grind)
    | exact superpose eq16 eq2414
    | exact resolve eq2414 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2967 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ (M.op X0 (M.op X1 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X0 (M.op X1 x))
       have i₂ := eq2414 x X0 X1
       grind)
    | exact superpose eq2414 eq35
    | exact resolve eq35 eq2414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2414
  have eq2978 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ (M.op X0 (M.op X1 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2967 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2967
    | (have j0 := eq2967 X0 X1
       grind)
    | exact resolve eq2967 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2967
  have eq3102 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (M.op X0 (σ x)) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op (M.op X0 sF2) sF2)
       have i₂ := eq2948 X0 sF2
       grind)
    | exact superpose eq2948 eq90
    | exact resolve eq90 eq2948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq2948
  have eq3105 : ∀ X0 : G, x = (k x (τ (M.op (M.op X0 (σ x)) (σ x)))) := by
    intro X0
    first
    | exact superpose eq29 eq3102
    | exact resolve eq3102 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102
  have eq3135 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ (M.op (M.op X0 (M.op X1 x)) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq2978 x x
       have i₂ := eq183 X0 X1 x x x
       grind)
    | exact superpose eq183 eq2978
    | exact resolve eq2978 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq2978
  have eq4267 : ∀ X0 : G, (k (M.op x y) y) = (M.op X0 (M.op x y)) ∨ y = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq192 eq913
    | exact resolve eq913 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq4473 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq672
       grind)
    | exact superpose eq672 eq40
    | exact resolve eq40 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq4474 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4473
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4473
    | exact resolve eq4473 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4473
  have eq4476 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq4474
    | exact resolve eq4474 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4474
  have eq4871 : ∀ X0 : G, (k (M.op x y) y) = (M.op (M.op x y) y) ∨ y = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4267 eq192
    | (have j1 := eq4267 X0
       grind)
    | exact resolve eq192 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4267
  have eq5199 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x y))) = (k (M.op (M.op X0 y) y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op X0 y) y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 y) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 X0 X1 X2
       have i₂ := eq11 (M.op (M.op X0 y) y) sF0
       grind)
    | exact superpose eq11 eq201
    | (have j1 := eq11 (M.op (M.op X0 y) y) (M.op x y)
       grind)
    | exact resolve eq201 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq5302 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x y))) = (k (M.op (M.op x y) y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op X0 y) y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 y) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5199 X0 X1 X2
       have i₂ := eq211 X0
       grind)
    | (have i₁ := eq5199 x X1 X2
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq5199
    | (have j0 := eq5199 X0 X1 X2
       grind)
    | exact resolve eq5199 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5199
  have eq5322 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op X0 y) y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | exact superpose eq215 eq5302
    | (have j0 := eq5302 X0 x x
       grind)
    | exact resolve eq5302 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq5302
  have eq5334 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op X0 y) y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq5322 X0
       have j1 := eq1958 X0 x y (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq5322 X0
       have r₂ := eq1958 (M.op (M.op X0 y) y) x y (M.op x y) x
       grind)
    | (have r₁ := eq5322 X0
       have r₂ := eq1958 (M.op x y) (M.op X0 y) y (M.op x y) x
       grind)
    | exact resolve eq5322 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq5322
  have eq5338 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have j1 := eq425 x (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq5334 x
       have r₂ := eq425 (M.op (M.op x y) y) (M.op x y) x
       grind)
    | exact resolve eq5334 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq5334
  have eq5342 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq192 eq5338
    | exact resolve eq5338 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5338
  have eq5366 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (k (σ (M.op X0 (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5342 eq41
    | exact resolve eq41 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq5342
  have eq6756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4476 eq674
    | exact resolve eq674 eq4476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4476
  have eq6765 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq6756
       have r₂ := eq27
       grind)
    | exact resolve eq6756 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6756
  have eq6772 : x = (k x (τ (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6765 eq3105
    | exact resolve eq3105 eq6765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105
  have eq6803 : x = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6765 eq6772
    | exact resolve eq6772 eq6765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6765 eq6772
  have eq6807 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq6803
    | exact resolve eq6803 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6803
  have eq6809 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq6807
       have r₂ := eq13 x y
       grind)
    | exact resolve eq6807 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6807
  have eq6811 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq672
       have i₂ := eq6809
       grind)
    | exact superpose eq6809 eq672
    | exact resolve eq672 eq6809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq6809
  have eq6815 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6811
  have eq6850 : ∀ X0 X1 : G, (M.op y x) = (M.op X0 (M.op X1 x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq6815
       grind)
    | exact superpose eq6815 eq16
    | exact resolve eq16 eq6815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6852 : ∀ X0 : G, (M.op y x) = (M.op (M.op X0 x) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq180 X0 x y
       have i₂ := eq6815
       grind)
    | exact superpose eq6815 eq180
    | exact resolve eq180 eq6815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6870 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6815 eq6852
    | exact resolve eq6852 eq6815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6852
  have eq6872 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq6815 eq6850
    | exact resolve eq6850 eq6815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6815 eq6850
  have eq7072 : ∀ X1 X2 X3 : G, y = (M.op X1 (M.op X2 (M.op X3 x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq187 x x X1 X2 X3
       have i₂ := eq6870 x
       grind)
    | exact superpose eq6870 eq187
    | exact resolve eq187 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq6870
  have eq7116 : ∀ X1 : G, y = (M.op X1 y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f7116_14 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op X1 (M.op X2 x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1 X2
      grind
    have f7116_15 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f7116_24 : y ≠ (M.op x y) := by grind
    have f7116_25 : x ≠ (M.op x y) := by grind
    have f7116_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f7116_27 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f7116_15 X0 X1
         grind)
      | (have r₁ := f7116_15 X0 X1
         have r₂ := f7116_24
         grind)
      | exact resolve f7116_15 f7116_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7116_28 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op X1 (M.op X2 x))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1 X2
      first
      | (have j0 := f7116_14 X0 X1 X2
         grind)
      | (have r₁ := f7116_14 X0 X1 X2
         have r₂ := f7116_24
         grind)
      | exact resolve f7116_14 f7116_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7116_29 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f7116_27 X0 X1
         grind)
      | (have r₁ := f7116_27 X0 X1
         have r₂ := f7116_25
         grind)
      | exact resolve f7116_27 f7116_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7116_30 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op X1 (M.op X2 x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1 X2
      first
      | (have j0 := f7116_28 X0 X1 X2
         grind)
      | (have r₁ := f7116_28 X0 X1 X2
         have r₂ := f7116_25
         grind)
      | exact resolve f7116_28 f7116_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7116_31 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 x)) := by
      intro X0 X1
      first
      | (have j0 := f7116_29 X0 X1
         grind)
      | (have r₁ := f7116_29 X0 X1
         have r₂ := f7116_26
         grind)
      | exact resolve f7116_29 f7116_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7116_32 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op X1 (M.op X2 x))) := by
      intro X0 X1 X2
      first
      | (have j0 := f7116_30 X0 X1 X2
         grind)
      | (have r₁ := f7116_30 X0 X1 X2
         have r₂ := f7116_26
         grind)
      | exact resolve f7116_30 f7116_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7116_33 : ∀ X0 : G, y = (M.op X0 y) := by
      intro X0
      first
      | (have i₁ := f7116_32 X0 x x
         have i₂ := f7116_31 x x
         grind)
      | exact superpose f7116_31 f7116_32
      | exact resolve f7116_32 f7116_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7116_36 : y ≠ y := by
      first
      | (have i₁ := f7116_24
         have i₂ := f7116_33 x
         grind)
      | exact superpose f7116_33 f7116_24
      | (have r₁ := f7116_24
         have r₂ := f7116_33 x
         grind)
      | exact resolve f7116_24 f7116_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7116_37 : False := by grind
    exact f7116_37
  clear eq6872 eq7072
  have eq7192 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7116 x
       grind)
    | exact superpose eq7116 eq18
    | (have j1 := eq7116 x
       grind)
    | exact resolve eq18 eq7116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7116
  have eq7204 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7192
  have eq7218 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq7204 eq247
    | exact resolve eq247 eq7204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7732 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7218 eq26
    | (have j1 := eq7218 X0 (σ x)
       grind)
    | exact resolve eq26 eq7218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7218
  have eq7750 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7204 eq7732
    | exact resolve eq7732 eq7204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7204 eq7732
  have eq7863 : y = (k y (τ (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7750 eq594
    | exact resolve eq594 eq7750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7750
  have eq7876 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq7863
    | exact resolve eq7863 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7863
  have eq7921 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq725 y y
       have i₂ := eq7876
       grind)
    | exact superpose eq7876 eq725
    | (have j0 := eq725 y y
       grind)
    | (have r₁ := eq725 y y
       have r₂ := eq7876
       grind)
    | exact resolve eq725 eq7876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7876
  have eq7922 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7921
  have eq7923 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7922
  have eq7934 : (M.op (M.op x y) y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq211 y
       have i₂ := eq7923
       grind)
    | exact superpose eq7923 eq211
    | exact resolve eq211 eq7923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq7970 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7923 eq7934
    | exact resolve eq7934 eq7923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7923 eq7934
  have eq7990 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7970 eq184
    | exact resolve eq184 eq7970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7970
  have eq8704 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7990 x
       grind)
    | exact superpose eq7990 eq18
    | (have j1 := eq7990 x
       grind)
    | exact resolve eq18 eq7990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7990
  have eq8716 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8704
  have eq8724 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8716
       grind)
    | exact superpose eq8716 eq18
    | exact resolve eq18 eq8716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8725 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8716
       grind)
    | exact superpose eq8716 eq24
    | exact resolve eq24 eq8716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8765 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8725
    | exact resolve eq8725 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8725
  have eq8766 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq192 eq8724
    | exact resolve eq8724 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8724
  have eq8767 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8716 eq8766
    | exact resolve eq8766 eq8716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8716 eq8766
  have eq8846 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8767 eq5366
    | exact resolve eq5366 eq8767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5366 eq8767
  have eq8878 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8846
    | exact resolve eq8846 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8846
  have eq8890 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8765 eq8878
    | exact resolve eq8878 eq8765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8878
  have eq9065 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8890 eq725
    | (have j0 := eq725 (σ y) (σ y)
       grind)
    | (have r₁ := eq725 (σ y) (σ y)
       have r₂ := eq8890
       grind)
    | exact resolve eq725 eq8890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8890
  have eq9066 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9065
  have eq9067 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9066
  have eq9084 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9067 eq265
    | exact resolve eq265 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq9126 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9067 eq9084
    | exact resolve eq9084 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9067 eq9084
  have eq9145 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9126 eq185
    | exact resolve eq185 eq9126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq9126
  have eq9393 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9145 eq26
    | (have j1 := eq9145 (σ x)
       grind)
    | exact resolve eq26 eq9145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9145
  have eq9436 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9393 eq27
    | exact resolve eq27 eq9393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9393
  have eq9490 : x = (M.op x y) := by
    first
    | (have r₁ := eq9436
       have r₂ := eq8765
       grind)
    | exact resolve eq9436 eq8765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8765 eq9436
  have eq9497 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9490
       grind)
    | exact superpose eq9490 eq18
    | exact resolve eq18 eq9490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9498 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9490
       grind)
    | exact superpose eq9490 eq22
    | exact resolve eq22 eq9490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq9507 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3135 X0 X1
       have i₂ := eq9490
       grind)
    | exact superpose eq9490 eq3135
    | exact resolve eq3135 eq9490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq9521 : (σ x) = (k (σ x) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq192 eq9507
    | exact resolve eq9507 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq9507
  have eq9528 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq9497 eq9521
    | exact resolve eq9521 eq9497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9521
  have eq9532 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq9528
    | exact resolve eq9528 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9528
  have eq9537 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9498 eq20
    | exact resolve eq20 eq9498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9548 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq9498 eq1224
    | exact resolve eq1224 eq9498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq9645 : ∀ X0 : G, (M.op x y) = (k (M.op x y) y) ∨ y = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq9497 eq4871
    | (have j0 := eq4871 X0
       grind)
    | exact resolve eq4871 eq9497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4871
  have eq9650 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq9497 eq184
    | exact resolve eq184 eq9497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq9497
  have eq9700 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have j1 := eq242 x y
       grind)
    | (have r₁ := eq9645 x
       have r₂ := eq242 x y
       grind)
    | exact resolve eq9645 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq9645
  have eq10815 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq9532 eq725
    | (have j0 := eq725 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq725 eq9532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9532
  have eq10817 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq10815
       have r₂ := eq9537
       grind)
    | exact resolve eq10815 eq9537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10815
  have eq10823 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq9537 eq10817
    | exact resolve eq10817 eq9537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10817
  have eq10828 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9537 eq10823
    | exact resolve eq10823 eq9537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10823
  have eq10829 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq10828
  have eq10858 : ∀ X1 X2 : G, (M.op x y) = (M.op X1 (M.op X2 y)) := by
    intro X1 X2
    first
    | exact superpose eq9650 eq197
    | exact resolve eq197 eq9650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq9650
  have eq11014 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq10829 eq180
    | exact resolve eq180 eq10829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq11036 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq10829 eq11014
    | exact resolve eq11014 eq10829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11014
  have eq11384 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq11036 eq16
    | exact resolve eq16 eq11036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11036
  have eq11446 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq10829 eq11384
    | exact resolve eq11384 eq10829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11384
  have eq12144 : (k (M.op x y) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq674 eq9548
    | exact resolve eq9548 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq9548
  have eq12209 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq31 eq12144
    | exact resolve eq12144 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12144
  have eq12241 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq9700 eq12209
    | exact resolve eq12209 eq9700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9700 eq12209
  have eq12264 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11446 eq12241
    | exact resolve eq12241 eq11446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11446 eq12241
  have eq15118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12264 eq14
    | exact resolve eq14 eq12264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12264
  have eq15129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15118
    | exact resolve eq15118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15118
  have eq15134 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15129
       have r₂ := eq27
       grind)
    | exact resolve eq15129 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15129
  have eq15142 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq15134 eq247
    | exact resolve eq247 eq15134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq15443 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq15142 eq26
    | (have j1 := eq15142 X0 (σ x)
       grind)
    | exact resolve eq26 eq15142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15142
  have eq15464 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq15134 eq15443
    | exact resolve eq15443 eq15134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15134 eq15443
  have eq15602 : y = (k y (τ (σ y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15464 eq594
    | exact resolve eq594 eq15464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq15464
  have eq15616 : y = (k y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq15602
    | exact resolve eq15602 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15602
  have eq15668 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq725 y y
       have i₂ := eq15616
       grind)
    | exact superpose eq15616 eq725
    | (have j0 := eq725 y y
       grind)
    | (have r₁ := eq725 y y
       have r₂ := eq15616
       grind)
    | exact resolve eq725 eq15616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq15616
  have eq15669 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq15668
  have eq15670 : y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq15669
  have eq15690 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq10858 X0 y
       have i₂ := eq15670
       grind)
    | exact superpose eq15670 eq10858
    | exact resolve eq10858 eq15670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10858
  have eq15845 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15670
       have i₂ := eq15690 y
       grind)
    | exact superpose eq15690 eq15670
    | exact resolve eq15670 eq15690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15670 eq15690
  have eq15862 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq15845
  have eq15904 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15862 eq31
    | exact resolve eq31 eq15862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15862
  have eq16007 : x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq15904
    | exact resolve eq15904 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15904
  have eq16024 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16007
       have i₂ := eq9490
       grind)
    | exact superpose eq9490 eq16007
    | exact resolve eq16007 eq9490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9490 eq16007
  have eq16025 : y = (M.op x y) := by grind
  clear eq16024
  have eq16035 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq16025
       grind)
    | exact superpose eq16025 eq24
    | exact resolve eq24 eq16025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16025
  have eq16087 : (σ x) = (σ y) := by
    first
    | exact superpose eq9498 eq16035
    | exact resolve eq16035 eq9498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9498 eq16035
  have eq16088 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16087 eq26
    | exact resolve eq26 eq16087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq16087
  have eq16181 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10829 eq16088
    | exact resolve eq16088 eq10829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10829 eq16088
  have eq16208 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq16181 eq27
    | exact resolve eq27 eq16181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16181
  have eq16278 : False := by grind
  exact eq16278

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_x_y_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq47 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq47 (σ X0)
       grind)
    | exact superpose eq47 eq15
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq61
    | exact resolve eq61 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq61
  have eq84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq84
    | (have j0 := eq84 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq84 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85 y x
       grind)
    | exact superpose eq85 eq16
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq622 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq282
       have i₂ := eq84 y x
       grind)
    | exact superpose eq84 eq282
    | (have j1 := eq84 (σ x) (σ y)
       grind)
    | (have r₁ := eq282
       have r₂ := eq84 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq282
       have r₂ := eq84 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq282 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq282
  have eq625 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq622
  have eq626 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq625
       grind)
    | exact superpose eq625 eq16
    | exact resolve eq16 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq627 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq626
       have r₂ := eq70 x
       grind)
    | exact resolve eq626 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq664 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq627
       grind)
    | exact superpose eq627 eq10
    | exact resolve eq10 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq681 : x = y := by
    first
    | (have i₁ := eq664
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq664
    | exact resolve eq664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq726 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq681
       grind)
    | exact superpose eq681 eq16
    | exact resolve eq16 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq727 : False := by grind
  exact eq727

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_pyy_pxy_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq186 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq688 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq688
       have i₂ := eq186 sF2
       grind)
    | exact superpose eq186 eq688
    | exact resolve eq688 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq763 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq683
       have i₂ := eq186 x
       grind)
    | exact superpose eq186 eq683
    | exact resolve eq683 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq881 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (k y x) = (M.op x x) := by
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
  have eq886 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq907 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq886
       have i₂ := eq186 sF2
       grind)
    | exact superpose eq186 eq886
    | exact resolve eq886 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq912 : (M.op x y) ≠ (k x x) ∨ (M.op x y) = (M.op y x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq881
       have i₂ := eq186 x
       grind)
    | exact superpose eq186 eq881
    | exact resolve eq881 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq928 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq907
       have i₂ := eq186 sF2
       grind)
    | exact superpose eq186 eq907
    | exact resolve eq907 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq933 : (M.op x y) ≠ (k x x) ∨ (k x x) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq912
       have i₂ := eq186 x
       grind)
    | exact superpose eq186 eq912
    | exact resolve eq912 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq912
  have eq6968 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq763
       grind)
    | exact superpose eq763 eq39
    | exact resolve eq39 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq6969 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq6968
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6968
    | exact resolve eq6968 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6968
  have eq6971 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq6969
    | exact resolve eq6969 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6969
  have eq108877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq6971 eq760
    | exact resolve eq760 eq6971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108888 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq108877
       have r₂ := eq27
       grind)
    | exact resolve eq108877 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108877
  have eq108901 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq108888 eq928
    | (have r₁ := eq928
       have r₂ := eq108888
       grind)
    | exact resolve eq928 eq108888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108888
  have eq109025 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq108901
  have eq109026 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq109025
  have eq109095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq6971 eq109026
    | exact resolve eq109026 eq6971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109026
  have eq109142 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq109095
       have r₂ := eq27
       grind)
    | exact resolve eq109095 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109095
  have eq109173 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq109142 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq109142
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq109142
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq109142
       grind)
    | exact resolve eq13 eq109142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109142
  have eq109292 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq109173
       have r₂ := eq26
       grind)
    | exact resolve eq109173 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109173
  have eq109317 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq6971 eq109292
    | exact resolve eq109292 eq6971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6971 eq109292
  have eq109323 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq109317
       have r₂ := eq27
       grind)
    | exact resolve eq109317 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109317
  have eq109331 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq933
       have i₂ := eq109323
       grind)
    | exact superpose eq109323 eq933
    | (have r₁ := eq933
       have r₂ := eq109323
       grind)
    | exact resolve eq933 eq109323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq109338 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq109323
       grind)
    | exact superpose eq109323 eq39
    | exact resolve eq39 eq109323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109323
  have eq109450 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq109331
  have eq109451 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq109450
  have eq109528 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq109338
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq109338
    | exact resolve eq109338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq109338
  have eq109585 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq109528
    | exact resolve eq109528 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109528
  have eq109623 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq109451
       grind)
    | exact superpose eq109451 eq39
    | exact resolve eq39 eq109451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109451
  have eq109627 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq109623
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq109623
    | exact resolve eq109623 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109623
  have eq109632 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq109627
    | exact resolve eq109627 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109627
  have eq109952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq109632 eq760
    | exact resolve eq760 eq109632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109963 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq109952
       have r₂ := eq27
       grind)
    | exact resolve eq109952 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109952
  have eq109970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq109585 eq109963
    | exact resolve eq109963 eq109585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109585 eq109963
  have eq109973 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq109970
       have r₂ := eq27
       grind)
    | exact resolve eq109970 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109970
  have eq109980 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq109973 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq109973
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq109973
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq109973
       grind)
    | exact resolve eq13 eq109973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109973
  have eq110103 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq109980
       have r₂ := eq26
       grind)
    | exact resolve eq109980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109980
  have eq110138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq109632 eq110103
    | exact resolve eq110103 eq109632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109632 eq110103
  have eq110148 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq110138
       have r₂ := eq27
       grind)
    | exact resolve eq110138 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110138
  have eq110155 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq110148
       grind)
    | exact superpose eq110148 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq110148
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq110148
       grind)
    | exact resolve eq13 eq110148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110148
  have eq110275 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq110155
       have r₂ := eq18
       grind)
    | exact resolve eq110155 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq110155
  have eq110311 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq110275
       grind)
    | exact superpose eq110275 eq39
    | exact resolve eq39 eq110275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq110275
  have eq110315 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq110311
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq110311
    | exact resolve eq110311 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq110311
  have eq110319 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq110315
    | exact resolve eq110315 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq110315
  have eq110334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq110319 eq760
    | exact resolve eq760 eq110319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq110347 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq110334
       have r₂ := eq27
       grind)
    | exact resolve eq110334 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110334
  have eq112312 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq110347 eq928
    | (have r₁ := eq928
       have r₂ := eq110347
       grind)
    | exact resolve eq928 eq110347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq110347
  have eq112438 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq112312
  have eq112439 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq112438
  have eq112508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq110319 eq112439
    | exact resolve eq112439 eq110319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112439
  have eq112555 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq112508
       have r₂ := eq27
       grind)
    | exact resolve eq112508 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112508
  have eq112586 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq112555 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq112555
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq112555
       grind)
    | exact resolve eq13 eq112555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112555
  have eq112706 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq112586
       have r₂ := eq26
       grind)
    | exact resolve eq112586 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq112586
  have eq112739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq110319 eq112706
    | exact resolve eq112706 eq110319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110319 eq112706
  have eq112754 : False := by grind
  exact eq112754

/-- `Equation575`: `x = y ◇ (z ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation575 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law575 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law575.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X1 X0))) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X3 (M.op X3 (M.op X1 X0))) X1 X2
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (k X0 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op x y))) = (M.op x (M.op X0 (M.op X0 y))) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq176 sF4
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : x ≠ (M.op x y) ∨ x = y ∨ y = (k x y) := by
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
  have eq554 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq187 eq187
    | exact resolve eq187 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X1 (M.op X2 (M.op X2 (M.op (σ x) (M.op X0 (M.op X0 (σ y))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq187 eq16
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq641 : ∀ X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X1 (M.op X2 (M.op X2 (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))))) := by
    intro X1 X2
    first
    | exact superpose eq192 eq636
    | exact resolve eq636 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq681 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 (k X0 X1)))) = X1 ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq681
       grind)
    | exact superpose eq681 eq40
    | exact resolve eq40 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq766 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq765
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq765
    | exact resolve eq765 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq768 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq766
    | exact resolve eq766 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq768 eq686
    | exact resolve eq686 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq776
       have r₂ := eq27
       grind)
    | exact resolve eq776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq791 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq783 eq554
    | (have r₁ := eq554
       have r₂ := eq783
       grind)
    | exact resolve eq554 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq794 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq791
  have eq795 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq794
  have eq800 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq795 eq768
    | exact resolve eq768 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq803 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq795 eq90
    | exact resolve eq90 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq795
  have eq806 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq800
  have eq810 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq803
    | exact resolve eq803 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq813 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq810
       have r₂ := eq551
       grind)
    | exact resolve eq810 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq810
  have eq817 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq681
       have i₂ := eq813
       grind)
    | exact superpose eq813 eq681
    | exact resolve eq681 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq818 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq813
       grind)
    | exact superpose eq813 eq35
    | exact resolve eq35 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq813
  have eq820 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq817
  have eq823 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq818
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq818
    | exact resolve eq818 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq828 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq823 eq686
    | exact resolve eq686 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq823
  have eq832 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq828
  have eq841 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq806 eq31
    | exact resolve eq31 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq863 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq841
    | exact resolve eq841 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq864 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq863
  have eq867 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq864 eq28
    | exact resolve eq28 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq888 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq867
    | exact resolve eq867 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq896 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op x (M.op X1 (M.op X1 (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq183 X1 X0
       have i₂ := eq888
       grind)
    | exact superpose eq888 eq183
    | exact resolve eq183 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq902 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq175 eq896
    | exact resolve eq896 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq906 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq888 eq902
    | exact resolve eq902 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq902
  have eq997 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq832 eq176
    | exact resolve eq176 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1001 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (σ y))) = (M.op X1 (M.op X1 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq832 eq632
    | exact resolve eq632 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq1008 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq192 eq997
    | exact resolve eq997 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1010 : (σ y) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq832 eq1008
    | exact resolve eq1008 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1139 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op X0 (M.op x y)) = X0 ∨ (M.op X0 (M.op x y)) = (k X0 (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq906 eq12
    | (have j0 := eq12 (M.op X0 (M.op x y)) X0
       grind)
    | (have r₁ := eq12 (M.op x y) (M.op (M.op x y) (M.op x y))
       have r₂ := eq906 (M.op x y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq906 X0
       grind)
    | exact resolve eq12 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq1658 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq1001
    | (have j0 := eq1001 (σ x) X0
       grind)
    | exact resolve eq1001 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1676 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq832 eq1658
    | exact resolve eq1658 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq1678 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq1676
    | (have j0 := eq1676 X0
       grind)
    | exact resolve eq1676 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676
  have eq1680 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq832 eq1678
    | exact resolve eq1678 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq1693 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ y)) = X0 ∨ (M.op X0 (σ y)) = (k X0 (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1680 eq12
    | (have j0 := eq12 (M.op X0 (σ y)) X0
       grind)
    | (have r₁ := eq12 (σ y) (M.op (σ y) (σ y))
       have r₂ := eq1680 (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1680 X0
       grind)
    | exact resolve eq12 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq1955 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have j0 := eq1139 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1956 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have j1 := eq13 (M.op x y) (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq1955
       have r₂ := eq13 (M.op x y) (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq1955
       have r₂ := eq13 (M.op (M.op x y) (M.op x y)) (M.op x y)
       grind)
    | (have r₁ := eq1955
       have r₂ := eq13 (M.op (M.op x y) (M.op x y)) (k (M.op x y) (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq1955 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq1957 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1956
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq1956
    | exact resolve eq1956 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq1958 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1957 eq37
    | exact resolve eq37 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1957
  have eq1960 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq41 eq1958
    | exact resolve eq1958 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq1961 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq1960
    | exact resolve eq1960 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq1962 : (k (σ y) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq864 eq1961
    | exact resolve eq1961 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq1961
  have eq2016 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op X1 (M.op X1 (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))))) := by
    intro X0 X1
    first
    | exact superpose eq184 eq177
    | exact resolve eq177 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq2215 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 x
       have i₂ := eq177 (M.op X1 X2) X1 x X0
       grind)
    | (have i₁ := eq16 X0 X1 X1
       have i₂ := eq177 (M.op X1 X0) X1 X2 X1
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2288 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq641 eq2016
    | exact resolve eq2016 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq2016
  have eq2371 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (σ y) (M.op X0 (M.op X0 (k (σ y) (σ y))))) ∨ (σ y) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1962 eq691
    | (have j0 := eq691 (σ y) (k (σ y) (σ y)) x
       grind)
    | exact resolve eq691 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962
  have eq2408 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2371 x
       have i₂ := eq178 sF3 x
       grind)
    | exact superpose eq178 eq2371
    | exact resolve eq2371 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq2409 : (σ y) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2408
  have eq2529 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2409 eq178
    | exact resolve eq178 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2546 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2288 eq2529
    | exact resolve eq2529 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529
  have eq2835 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2546 eq178
    | exact resolve eq178 eq2546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546
  have eq2844 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2288 eq2835
    | (have j0 := eq2835 (σ x)
       grind)
    | exact resolve eq2835 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2835
  have eq2895 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2844 eq16
    | exact resolve eq16 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2904 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2288 eq2895
    | (have j0 := eq2895 (σ x)
       grind)
    | exact resolve eq2895 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2288 eq2895
  have eq2913 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2844 eq2904
    | exact resolve eq2904 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844 eq2904
  have eq2914 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2913
  have eq2925 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq783 eq2914
    | exact resolve eq2914 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq2914
  have eq2936 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2925
  have eq2947 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2936
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq2936
    | exact resolve eq2936 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936
  have eq3017 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2947 eq97
    | exact resolve eq97 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2947
  have eq3039 : y = (k x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq3017
    | exact resolve eq3017 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017
  have eq3045 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq820 eq3039
    | exact resolve eq3039 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq3039
  have eq3091 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op X0 (M.op x y)))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq178 x X0
       have i₂ := eq3045
       grind)
    | exact superpose eq3045 eq178
    | exact resolve eq178 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq3092 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq175 eq3091
    | exact resolve eq3091 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091
  have eq3093 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3092
  have eq3097 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3093 eq31
    | exact resolve eq31 eq3093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093
  have eq3136 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq3097
    | exact resolve eq3097 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3097
  have eq3137 : x = (M.op x y) ∨ x = y := by grind
  clear eq3136
  have eq3151 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq3137
       grind)
    | exact superpose eq3137 eq22
    | exact resolve eq22 eq3137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3154 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op X0 (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq3137
       grind)
    | exact superpose eq3137 eq175
    | exact resolve eq175 eq3137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq3137
  have eq3164 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq3151
    | exact resolve eq3151 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151
  have eq3297 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op x y) (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3154 eq177
    | exact resolve eq177 eq3154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154
  have eq3317 : ∀ X0 : G, y = (M.op X0 (M.op X0 (k (M.op x y) (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3297 X0
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq3297
    | exact resolve eq3297 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3297
  have eq3451 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 (k (M.op x y) (M.op x y)))))) = (M.op X1 (M.op X2 y)) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq3317 eq177
    | exact resolve eq177 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq3317
  have eq4705 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (k (M.op x y) (M.op x y)))) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 y)))) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq3451 eq16
    | exact resolve eq16 eq3451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451
  have eq4827 : ∀ X0 X1 : G, (M.op X0 (M.op y (k (M.op x y) (M.op x y)))) = (M.op X1 (M.op X1 (M.op X0 (k y y)))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq4705 X0 y X1
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq4705
    | exact resolve eq4705 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4705
  have eq4890 : ∀ X0 : G, (k y y) = (M.op X0 (M.op X0 (M.op y (k (M.op x y) (M.op x y))))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 (k y y) X0 x
       have i₂ := eq4827 X0 x
       grind)
    | exact superpose eq4827 eq16
    | exact resolve eq16 eq4827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4827
  have eq4976 : (k (M.op x y) (M.op x y)) = (M.op y (k y y)) ∨ x = y := by
    first
    | exact superpose eq4890 eq16
    | exact resolve eq16 eq4890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4983 : ∀ X0 : G, (M.op X0 (M.op X0 (k y y))) = (M.op y (k (M.op x y) (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4890 eq16
    | exact resolve eq16 eq4890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4890
  have eq5040 : (M.op y (k (M.op x y) (M.op x y))) = (M.op (k y y) (k (k y y) (k y y))) ∨ x = y := by
    first
    | (have i₁ := eq4983 (k y y)
       have i₂ := eq174 (k y y)
       grind)
    | exact superpose eq174 eq4983
    | exact resolve eq4983 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4983
  have eq6163 : ∀ X0 : G, (k (k y y) (k y y)) = (M.op X0 (M.op X0 (M.op (k y y) (M.op y (k (M.op x y) (M.op x y)))))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2215 X0 (k y y) (k (k y y) (k y y))
       have i₂ := eq5040
       grind)
    | exact superpose eq5040 eq2215
    | exact resolve eq2215 eq5040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5040
  have eq12035 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq1693 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq12036 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 (σ y) (M.op (σ y) (σ y))
       grind)
    | (have r₁ := eq12035
       have r₂ := eq13 (σ y) (M.op (σ y) (σ y))
       grind)
    | (have r₁ := eq12035
       have r₂ := eq13 (M.op (σ y) (σ y)) (σ y)
       grind)
    | (have r₁ := eq12035
       have r₂ := eq13 (M.op (σ y) (σ y)) (k (σ y) (M.op (σ y) (σ y)))
       grind)
    | exact resolve eq12035 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12035
  have eq12037 : (k (σ y) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12036
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq12036
    | exact resolve eq12036 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12036
  have eq12044 : (τ (k (σ y) (σ y))) = (k y (τ (k (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12037 eq107
    | exact resolve eq107 eq12037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq12037
  have eq12055 : (k y y) = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq115 eq12044
    | exact resolve eq12044 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq12044
  have eq12074 : ∀ X0 : G, (k y y) = (M.op y (M.op X0 (M.op X0 (k y y)))) ∨ y = (M.op y (k y y)) ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq691 y (k y y) X0
       have i₂ := eq12055
       grind)
    | exact superpose eq12055 eq691
    | (have j0 := eq691 y (k y y) x
       grind)
    | exact resolve eq691 eq12055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq12055
  have eq12091 : y = (k y y) ∨ y = (M.op y (k y y)) ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12074 x
       have i₂ := eq178 y x
       grind)
    | exact superpose eq178 eq12074
    | exact resolve eq12074 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12074
  have eq12092 : y = (M.op y (k y y)) ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12091
  have eq12104 : y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4976
       have i₂ := eq12092
       grind)
    | exact superpose eq12092 eq4976
    | exact resolve eq4976 eq12092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4976 eq12092
  have eq12125 : y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq12104
  have eq12221 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12125 eq41
    | exact resolve eq41 eq12125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12125
  have eq12266 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq12221
    | exact resolve eq12221 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12221
  have eq12293 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12266
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12266
    | exact resolve eq12266 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12266
  have eq12314 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3164 eq12293
    | exact resolve eq12293 eq3164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12293
  have eq12372 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) ∨ x = y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq12314 eq178
    | exact resolve eq178 eq12314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12314
  have eq12395 : (σ x) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq192 eq12372
    | exact resolve eq12372 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12372
  have eq12400 : (σ x) = (M.op (σ y) (k (σ y) (σ y))) ∨ x = y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq832 eq12395
    | exact resolve eq12395 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12395
  have eq12573 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12400 eq1010
    | exact resolve eq1010 eq12400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010 eq12400
  have eq12593 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12573
  have eq12621 : ∀ X0 : G, (k y y) = (M.op X0 (M.op X0 (M.op y (M.op y (k (M.op x y) (M.op x y)))))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6163 X0
       have i₂ := eq12593
       grind)
    | exact superpose eq12593 eq6163
    | exact resolve eq6163 eq12593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163
  have eq12627 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq12593
       grind)
    | exact superpose eq12593 eq40
    | exact resolve eq40 eq12593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq12637 : ∀ X0 : G, (k y y) = (M.op X0 (M.op X0 (M.op y (M.op y (k (M.op x y) (M.op x y)))))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq12621 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12621
  have eq12655 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12627
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12627
    | exact resolve eq12627 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12627
  have eq12657 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12637 x
       have i₂ := eq2215 x y (k sF0 sF0)
       grind)
    | exact superpose eq2215 eq12637
    | exact resolve eq12637 eq2215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2215 eq12637
  have eq12666 : y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12593 eq12657
    | exact resolve eq12657 eq12593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12593 eq12657
  have eq12782 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12666 eq41
    | exact resolve eq41 eq12666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq12666
  have eq12827 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq12782
    | exact resolve eq12782 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12782
  have eq12855 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12827
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12827
    | exact resolve eq12827 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12827
  have eq12878 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3164 eq12855
    | exact resolve eq12855 eq3164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12855
  have eq12948 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq12878 eq178
    | exact resolve eq178 eq12878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq12878
  have eq12971 : (σ x) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq192 eq12948
    | exact resolve eq12948 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq12948
  have eq12976 : (σ x) = (M.op (σ y) (k (σ y) (σ y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq832 eq12971
    | exact resolve eq12971 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq12971
  have eq12980 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12655 eq12976
    | exact resolve eq12976 eq12655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12976
  have eq12983 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12980
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq12980
    | exact resolve eq12980 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12980
  have eq13004 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12983 eq12655
    | exact resolve eq12655 eq12983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12655 eq12983
  have eq13010 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13004
  have eq13033 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13010 eq27
    | exact resolve eq27 eq13010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13010
  have eq13088 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13033
       have r₂ := eq3164
       grind)
    | exact resolve eq13033 eq3164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3164 eq13033
  have eq13091 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq13088 eq31
    | exact resolve eq31 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq13088
  have eq13148 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq13091
    | exact resolve eq13091 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13091
  have eq13149 : x = y := by grind
  clear eq13148
  have eq13163 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13149
       grind)
    | exact superpose eq13149 eq18
    | exact resolve eq18 eq13149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq13164 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq13149
       grind)
    | exact superpose eq13149 eq24
    | exact resolve eq24 eq13149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13149
  have eq13172 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13164
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13164
    | exact resolve eq13164 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13164
  have eq13173 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13163
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq13163
    | exact resolve eq13163 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13163
  have eq13174 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13172 eq26
    | exact resolve eq26 eq13172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13172
  have eq13217 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq13174
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq13174
    | exact resolve eq13174 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq13174
  have eq13220 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq13173
       grind)
    | exact superpose eq13173 eq39
    | exact resolve eq39 eq13173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq13173
  have eq13222 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq13220
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13220
    | exact resolve eq13220 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13220
  have eq13224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13217 eq13222
    | exact resolve eq13222 eq13217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13217 eq13222
  have eq13226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13224
    | exact resolve eq13224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13224
  have eq13228 : False := by grind
  exact eq13228

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq203 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq84 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq206 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq207 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq206 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq209 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq207
    | (have j0 := eq207 X0 X1
       grind)
    | exact resolve eq207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq213 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq209 X0 X1
       have j1 := eq205 X0 X1
       grind)
    | (have r₁ := eq209 X0 X1
       have r₂ := eq205 X0 X1
       grind)
    | (have r₁ := eq209 (k X0 X1) X0
       have r₂ := eq205 X0 X1
       grind)
    | (have r₁ := eq209 X0 X0
       have r₂ := eq205 X0 X0
       grind)
    | exact resolve eq209 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq209
  have eq524 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq213 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq213
    | exact resolve eq213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq213 x y
       grind)
    | exact superpose eq213 eq16
    | (have j1 := eq213 x y
       grind)
    | exact resolve eq16 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq546 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq524 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq524
    | (have j0 := eq524 X0 X1
       grind)
    | exact resolve eq524 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq524
  have eq548 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq546
    | exact resolve eq546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq607 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq548 (τ X0) X1
       grind)
    | exact superpose eq548 eq18
    | (have j1 := eq548 (τ X0) X1
       grind)
    | exact resolve eq18 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq548
  have eq844 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq607 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq607
    | exact resolve eq607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq897 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq844
    | (have j0 := eq844 X0 X1
       grind)
    | exact resolve eq844 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq957 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq532
       have i₂ := eq897 x y
       grind)
    | exact superpose eq897 eq532
    | (have j1 := eq897 (σ x) (σ y)
       grind)
    | (have r₁ := eq532
       have r₂ := eq897 x y
       grind)
    | exact resolve eq532 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq957
  have eq965 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq958
  have eq1011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq532
       have i₂ := eq965
       grind)
    | exact superpose eq965 eq532
    | exact resolve eq532 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq965
  have eq1012 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1011
  have eq1013 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1012
  have eq1026 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1013
  have eq1033 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1026
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1026
    | exact resolve eq1026 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1070 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1033
       grind)
    | exact superpose eq1033 eq16
    | exact resolve eq16 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1081 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1070
       have i₂ := eq897 x y
       grind)
    | exact superpose eq897 eq1070
    | (have j1 := eq897 x y
       grind)
    | (have r₁ := eq1070
       have r₂ := eq897 x y
       grind)
    | exact resolve eq1070 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq1082 : x = (M.op y y) := by grind
  clear eq1081
  have eq1121 : (M.op x y) = (k x y) := by grind
  clear eq1082
  have eq1127 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1070
       have i₂ := eq1121
       grind)
    | exact superpose eq1121 eq1070
    | exact resolve eq1070 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq1121
  have eq1130 : False := by grind
  exact eq1130

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq532 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq73 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq73 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq73 X0 X1
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq537 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq532 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq538 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq537 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq543 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq538
    | (have j0 := eq538 X0 X1
       grind)
    | exact resolve eq538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq544 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq543 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq3279 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq544 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq544
    | (have j0 := eq544 X0 y
       grind)
    | exact resolve eq544 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq544
  have eq13585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13585
    | exact resolve eq13585 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13585
  have eq13597 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13586
       have r₂ := eq28
       grind)
    | exact resolve eq13586 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13586
  have eq13599 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13597
    | exact resolve eq13597 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13597
  have eq13602 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13599 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13599
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13599
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13599
       grind)
    | exact resolve eq12 eq13599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13599
  have eq13609 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq13602
  have eq13610 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13609
       have r₂ := eq27
       grind)
    | exact resolve eq13609 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13609
  have eq13618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13610 eq93
    | exact resolve eq93 eq13610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13610
  have eq13627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq13618
  have eq13630 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq13627
       have r₂ := eq28
       grind)
    | exact resolve eq13627 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13627
  have eq13871 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq13630
  have eq13882 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq27 eq13871
    | exact resolve eq13871 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13871
  have eq13889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq13882 eq93
    | exact resolve eq93 eq13882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq13882
  have eq13897 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq13889
  have eq13899 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13897
       have r₂ := eq28
       grind)
    | exact resolve eq13897 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13897
  have eq14142 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq13899
       grind)
    | exact superpose eq13899 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13899
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13899
       grind)
    | exact resolve eq12 eq13899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13899
  have eq14149 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq14142
  have eq14150 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14149
       have r₂ := eq19
       grind)
    | exact resolve eq14149 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14149
  have eq14154 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq14150
       grind)
    | exact superpose eq14150 eq70
    | exact resolve eq70 eq14150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14150
  have eq14174 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq14154
    | exact resolve eq14154 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14154
  have eq14189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14174 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq14174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14189
    | exact resolve eq14189 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14189
  have eq14205 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14194
       have r₂ := eq28
       grind)
    | exact resolve eq14194 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14194
  have eq14207 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14205
    | exact resolve eq14205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14205
  have eq14987 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14207 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14207
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14207
       grind)
    | exact resolve eq12 eq14207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14207
  have eq14994 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq14987
  have eq14995 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14994
       have r₂ := eq27
       grind)
    | exact resolve eq14994 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14994
  have eq15138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14995 eq14174
    | exact resolve eq14174 eq14995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14995
  have eq15141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq15138
  have eq15152 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15141
       have r₂ := eq28
       grind)
    | exact resolve eq15141 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15141
  have eq15160 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq15152
  have eq15171 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15160
    | exact resolve eq15160 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15160
  have eq15313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15171 eq14174
    | exact resolve eq14174 eq15171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14174 eq15171
  have eq15315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq15313
  have eq15325 : y = (M.op x x) := by
    first
    | (have r₁ := eq15315
       have r₂ := eq28
       grind)
    | exact resolve eq15315 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15315
  have eq15333 : (M.op x y) = (k y x) := by grind
  clear eq15325
  have eq15344 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq15333
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15333
    | exact resolve eq15333 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15333
  have eq15347 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq15344
       grind)
    | exact superpose eq15344 eq70
    | exact resolve eq70 eq15344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15344
  have eq15365 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq15347
    | exact resolve eq15347 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq15347
  have eq15905 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3279 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3279
    | (have j0 := eq3279 x
       grind)
    | exact resolve eq3279 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3279
  have eq15921 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15905
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq15905
    | exact resolve eq15905 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq15905
  have eq15944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15365 eq15921
    | exact resolve eq15921 eq15365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15921
  have eq15956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq15944
    | exact resolve eq15944 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15944
  have eq15965 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq15956
       have r₂ := eq28
       grind)
    | exact resolve eq15956 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15956
  have eq15979 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq15965
  have eq15990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15365 eq15979
    | exact resolve eq15979 eq15365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15365 eq15979
  have eq15992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15990
    | exact resolve eq15990 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15990
  have eq15993 : False := by grind
  exact eq15993
