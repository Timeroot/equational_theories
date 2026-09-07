import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation335 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law335 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X1
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X0 X1)
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq43
    | exact resolve eq43 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq59 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq27 (τ X1) X0
       grind)
    | exact superpose eq27 eq18
    | (have j1 := eq27 (τ X1) X0
       grind)
    | exact resolve eq18 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 (σ X1) (σ X0)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq28 X1 (τ X0)
       grind)
    | exact superpose eq28 eq17
    | (have j1 := eq28 X1 (τ X0)
       grind)
    | exact resolve eq17 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq28
  have eq93 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq37
  have eq108 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq93
    | exact resolve eq93 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq136 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X0 X1) X0
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq62
    | (have j0 := eq62 (M.op X0 X1) X0
       grind)
    | exact resolve eq62 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq146 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x y
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X1) (σ X0)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq224 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0 X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq44
    | exact resolve eq44 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq285 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq224 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq224
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq224 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq224 X0
       grind)
    | exact superpose eq224 eq62
    | (have j0 := eq62 (M.op X0 X0) (M.op X0 X0)
       grind)
    | (have r₁ := eq62 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq224 X0
       grind)
    | exact resolve eq62 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq296 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq294 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq835 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59
    | exact resolve eq59 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq875 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq835 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq835
    | (have j0 := eq835 X0 X1
       grind)
    | exact resolve eq835 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq934 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq982 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq934 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq934
    | (have j0 := eq934 X0 X1
       grind)
    | exact resolve eq934 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1694 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq158
       have i₂ := eq285 y x
       grind)
    | exact superpose eq285 eq158
    | (have j1 := eq285 y x
       grind)
    | exact resolve eq158 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1695 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq158
       have i₂ := eq982 x y
       grind)
    | exact superpose eq982 eq158
    | (have j1 := eq982 x y
       grind)
    | (have r₁ := eq158
       have r₂ := eq982 x y
       grind)
    | exact resolve eq158 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq1696 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq158
       have i₂ := eq875 y x
       grind)
    | exact superpose eq875 eq158
    | (have j1 := eq875 y x
       grind)
    | (have r₁ := eq158
       have r₂ := eq875 y x
       grind)
    | exact resolve eq158 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq875
  have eq1699 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq1696
  have eq1700 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1695
  have eq1701 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq1694
  have eq1885 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq2067 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq146
    | (have j0 := eq146 X1 (τ X0)
       grind)
    | exact resolve eq146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq2175 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2067 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2067
    | (have j0 := eq2067 X0 X1
       grind)
    | exact resolve eq2067 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2067
  have eq2185 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2175 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2175
    | (have j0 := eq2175 X0 X1
       grind)
    | exact resolve eq2175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq3436 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq108 x
       have i₂ := eq1699
       grind)
    | exact superpose eq1699 eq108
    | exact resolve eq108 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1699
  have eq3457 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3436
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3436
    | exact resolve eq3436 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3436
  have eq3458 : x = (k x y) := by grind
  clear eq3457
  have eq9872 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1700
       grind)
    | exact superpose eq1700 eq8
    | exact resolve eq8 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10858 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq296 (σ x)
       have i₂ := eq1701
       grind)
    | exact superpose eq1701 eq296
    | exact resolve eq296 eq1701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq1701
  have eq10871 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10858
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq10858
    | exact resolve eq10858 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10858
  have eq11064 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq10871
       grind)
    | exact superpose eq10871 eq9
    | exact resolve eq9 eq10871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10871
  have eq11161 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11064
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq11064
    | exact resolve eq11064 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11064
  have eq11163 : y = (k y y) := by
    first
    | (have j1 := eq62 y y
       grind)
    | (have r₁ := eq11161
       have r₂ := eq62 y y
       grind)
    | exact resolve eq11161 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11161
  have eq11321 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq11163
       grind)
    | exact superpose eq11163 eq178
    | (have j0 := eq178 y
       grind)
    | exact resolve eq178 eq11163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq11330 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq285 y y
       have i₂ := eq11163
       grind)
    | exact superpose eq11163 eq285
    | (have j0 := eq285 y x
       grind)
    | exact resolve eq285 eq11163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq11333 : y = (M.op y y) := by grind
  clear eq11330
  have eq11337 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq11321
  have eq11451 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1885 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq1885
    | (have j0 := eq1885 (τ X0) (τ X1)
       grind)
    | exact resolve eq1885 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq11456 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1885 x y
       have i₂ := eq3458
       grind)
    | exact superpose eq3458 eq1885
    | (have j0 := eq1885 x y
       grind)
    | exact resolve eq1885 eq3458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq11520 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11451 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq11451
    | (have j0 := eq11451 X0 X1
       grind)
    | exact resolve eq11451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11451
  have eq11526 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11520 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq11520
    | (have j0 := eq11520 X0 X1
       grind)
    | exact resolve eq11520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11520
  have eq11529 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11526 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11526
    | (have j0 := eq11526 X0 X1
       grind)
    | exact resolve eq11526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11526
  have eq11530 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11529 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11529
    | (have j0 := eq11529 X0 X1
       grind)
    | exact resolve eq11529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11529
  have eq11847 : x ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11530 x y
       have i₂ := eq3458
       grind)
    | exact superpose eq3458 eq11530
    | (have j0 := eq11530 x y
       grind)
    | exact resolve eq11530 eq3458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458 eq11530
  have eq12031 : ∀ X0 : G, y = X0 ∨ (M.op y X0) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq11163
       have i₂ := eq2185 y X0
       grind)
    | (have i₁ := eq11163
       have i₂ := eq2185 X0 (k y y)
       grind)
    | exact superpose eq2185 eq11163
    | (have j1 := eq2185 y X0
       grind)
    | exact resolve eq11163 eq2185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185 eq11163
  have eq12034 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq12031 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12031
  have eq16261 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq136 (σ x) (σ x)
       have i₂ := eq1700
       grind)
    | exact superpose eq1700 eq136
    | exact resolve eq136 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq1700
  have eq16307 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16261
       have r₂ := eq9872
       grind)
    | exact resolve eq16261 eq9872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9872 eq16261
  have eq16334 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16307
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq16307
    | exact resolve eq16307 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16307
  have eq18729 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq16334
       grind)
    | exact superpose eq16334 eq9
    | exact resolve eq9 eq16334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16334
  have eq18856 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18729
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq18729
    | exact resolve eq18729 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18729
  have eq19055 : y = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12034 x
       have i₂ := eq18856
       grind)
    | exact superpose eq18856 eq12034
    | (have j0 := eq12034 (M.op y x)
       grind)
    | exact resolve eq12034 eq18856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034 eq18856
  have eq19072 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19055
       have r₂ := eq11847
       grind)
    | exact resolve eq19055 eq11847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11847 eq19055
  have eq19269 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 x y
       have i₂ := eq19072
       grind)
    | exact superpose eq19072 eq8
    | exact resolve eq8 eq19072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19072
  have eq19291 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19269
       have i₂ := eq11333
       grind)
    | exact superpose eq11333 eq19269
    | exact resolve eq19269 eq11333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11333 eq19269
  have eq19292 : y = (M.op x y) := by grind
  clear eq19291
  have eq19324 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq19292
       grind)
    | exact superpose eq19292 eq8
    | exact resolve eq8 eq19292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19343 : y = (M.op y x) := by
    first
    | (have i₁ := eq19324
       have i₂ := eq19292
       grind)
    | exact superpose eq19292 eq19324
    | exact resolve eq19324 eq19292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19324
  have eq19983 : y ≠ y ∨ y = (k y x) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq19343
       grind)
    | exact superpose eq19343 eq62
    | (have j0 := eq62 y x
       grind)
    | (have r₁ := eq62 y x
       have r₂ := eq19343
       grind)
    | exact resolve eq62 eq19343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq19343
  have eq19990 : y = (k y x) := by grind
  clear eq19983
  have eq20445 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq163 y x
       have i₂ := eq19990
       grind)
    | exact superpose eq19990 eq163
    | (have j0 := eq163 y x
       grind)
    | exact resolve eq163 eq19990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq19990
  have eq20454 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq20445
       have i₂ := eq11337
       grind)
    | exact superpose eq11337 eq20445
    | exact resolve eq20445 eq11337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20445
  have eq20455 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20454
       have i₂ := eq11337
       grind)
    | exact superpose eq11337 eq20454
    | exact resolve eq20454 eq11337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11337 eq20454
  have eq20456 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20455
       have r₂ := eq11456
       grind)
    | exact resolve eq20455 eq11456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11456 eq20455
  have eq21556 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20456
       grind)
    | exact superpose eq20456 eq14
    | exact resolve eq14 eq20456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20456
  have eq21608 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq21556
       have i₂ := eq19292
       grind)
    | exact superpose eq19292 eq21556
    | exact resolve eq21556 eq19292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19292 eq21556
  have eq21609 : False := by grind
  exact eq21609

/-- `Equation3350`: `x ◇ y = y ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3350 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3350 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3350.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    grind
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq20
    | exact resolve eq20 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq24 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X2 (M.op X1 X0)) ∨ (M.op X3 X0) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X2))) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = (k (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X1 (M.op X2 X2)) X2
       have i₂ := eq12 (M.op X1 (M.op X2 X2)) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 (M.op X0 (M.op X2 X2)))
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = (k (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X0 X1 X2
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq35
    | (have j0 := eq35 X0 X1 X2
       grind)
    | exact resolve eq35 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X2)) X3) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op X0 (M.op X2 X2)) X3
       have i₂ := eq8 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X2 X2) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op (M.op X2 X2) X0) X3
       have i₂ := eq19 X2 X0 (M.op X1 X1)
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X0) X1 X2
       have i₂ := eq19 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) X0) (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1
    grind
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq19 X1 X0 X0
       grind)
    | exact superpose eq19 eq61
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq66 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X2 X2) X0) X3) = (M.op X0 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq53 X0 x X2 X3
       have i₂ := eq8 X0 X3 x
       grind)
    | exact superpose eq8 eq53
    | exact resolve eq53 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq67 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op X2 X2)) X3) = (M.op X0 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq52 X0 x X2 X3
       have i₂ := eq8 X0 X3 x
       grind)
    | exact superpose eq8 eq52
    | exact resolve eq52 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27
    | exact resolve eq27 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq33 (τ X1) X0
       grind)
    | exact superpose eq33 eq17
    | (have j1 := eq33 (τ X1) X0
       grind)
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq28 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq46
  have eq143 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq129 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq129
    | exact resolve eq129 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq163 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X3 X1) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq32 X1 X0 (M.op X0 X1) X3
       grind)
    | exact superpose eq32 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       have j1 := eq32 X2 X1 X2 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq14
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq9
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq36 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq143
    | (have j1 := eq36 X1 X0
       grind)
    | exact resolve eq143 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq295 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq143 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq143
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq143 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq294
    | (have j0 := eq294 X0 X1
       grind)
    | exact resolve eq294 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq492 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 X2 (M.op X3 X3)
       have i₂ := eq58 X3 (M.op (M.op X1 X1) X2) X0
       grind)
    | (have i₁ := eq19 X1 X2 (M.op X3 X3)
       have i₂ := eq58 X0 (M.op (M.op X1 X1) X2) X3
       grind)
    | exact superpose eq58 eq19
    | exact resolve eq19 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X0 X0)) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq492 X3 x X2 X0
       have i₂ := eq19 x X2 (M.op X3 X3)
       grind)
    | exact superpose eq19 eq492
    | exact resolve eq492 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq549 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X3) = (k (M.op X1 X0) X3) ∨ (M.op X1 X1) = X3 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38 X0 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq38 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq38
    | (have j0 := eq38 X3 X1 X2
       have j1 := eq12 X1 X3
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (k (M.op X1 (M.op X2 X2)) X0) ∨ (M.op (M.op X1 (M.op X3 X3)) X0) = (k (M.op X1 (M.op X3 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X1 X2
       have i₂ := eq38 X0 X1 X3
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq38 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq38 eq21
    | (have j1 := eq38 X0 X1 X3
       grind)
    | exact resolve eq21 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq620 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k (M.op X1 (M.op X3 X3)) X0) ∨ (M.op X1 (M.op X2 X2)) = (k (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq572 X0 X1 X2 X3
       have i₂ := eq67 X1 X3 X0
       grind)
    | exact superpose eq67 eq572
    | (have j0 := eq572 X0 X1 X2 X3
       grind)
    | exact resolve eq572 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X3) = (k (M.op X0 (M.op X1 X1)) X3) ∨ (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X2 X2) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38 X0 (M.op (M.op X2 X2) X0) X2
       have i₂ := eq66 X0 X2 (M.op X2 X2)
       grind)
    | exact superpose eq66 eq38
    | (have j0 := eq38 X3 (M.op (M.op X2 X2) X0) X2
       grind)
    | exact resolve eq38 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq703 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X1 (M.op (M.op X3 X3) X0)) ∨ (M.op X4 X2) = (k X4 X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq32 X2 X1 (M.op (M.op X3 X3) X0) X4
       have i₂ := eq66 X0 X3 (M.op X1 X2)
       grind)
    | exact superpose eq66 eq32
    | (have j0 := eq32 X2 X1 X2 X4
       grind)
    | exact resolve eq32 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq704 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X2 (M.op (M.op X3 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 X0 (M.op (M.op X1 X1) X2)
       have i₂ := eq66 X2 X1 (M.op (M.op X3 X3) X0)
       grind)
    | exact superpose eq66 eq19
    | exact resolve eq19 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq710 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq704 X0 X1 X2 x
       have i₂ := eq19 x X0 X2
       grind)
    | exact superpose eq19 eq704
    | exact resolve eq704 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq711 : ∀ X0 X1 X2 X4 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) ∨ (M.op X4 X2) = (k X4 X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq703 X0 X1 X2 x X4
       have i₂ := eq19 x X0 X1
       grind)
    | exact superpose eq19 eq703
    | (have j0 := eq703 X0 X1 X2 x X4
       grind)
    | exact resolve eq703 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq715 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k (M.op X0 (M.op X1 X1)) X3) ∨ (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X2 X2) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq699 X0 X1 X2 X3
       have i₂ := eq67 X0 X1 X3
       grind)
    | exact superpose eq67 eq699
    | (have j0 := eq699 X0 X1 X2 X3
       grind)
    | exact resolve eq699 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq746 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 X2) X0)) = X3 ∨ (M.op X0 X3) = (k (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq715 X0 X1 X2 X3
       have i₂ := eq19 X2 X0 (M.op (M.op X2 X2) X0)
       grind)
    | exact superpose eq19 eq715
    | (have j0 := eq715 X0 X1 X2 X3
       grind)
    | exact resolve eq715 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq752 : ∀ X0 X1 X3 : G, (M.op X0 X0) = X3 ∨ (M.op X0 X3) = (k (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq746 X0 X1 x X3
       have i₂ := eq19 x X0 X0
       grind)
    | exact superpose eq19 eq746
    | (have j0 := eq746 X0 X1 x X3
       grind)
    | exact resolve eq746 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq956 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (M.op X2 X2) X0
       have i₂ := eq497 (M.op X2 X2) X0 X1
       grind)
    | (have i₁ := eq19 X2 (M.op X2 X2) X0
       have i₂ := eq497 X1 X0 (M.op X2 X2)
       grind)
    | exact superpose eq497 eq19
    | exact resolve eq19 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1119 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X0 X1
       have i₂ := eq710 X1 x X0
       grind)
    | exact superpose eq710 eq19
    | exact resolve eq19 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1153 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op X0 (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 X0 X1 (M.op (M.op X3 X3) X2)
       have i₂ := eq710 (M.op X0 (M.op X1 X1)) X3 X2
       grind)
    | exact superpose eq710 eq67
    | exact resolve eq67 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1154 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1153 X0 X1 X2 x
       have i₂ := eq19 x X2 X0
       grind)
    | exact superpose eq19 eq1153
    | exact resolve eq1153 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1317 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X1 X0
       have i₂ := eq1119 X1 X0
       grind)
    | (have i₁ := eq85 X1 X0
       have i₂ := eq1119 X0 X1
       grind)
    | exact superpose eq1119 eq85
    | (have j0 := eq85 X1 X0
       grind)
    | exact resolve eq85 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ X1 ∨ (k X1 (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1317 (M.op X2 X2) X1
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq1317 (M.op X2 X2) X1
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq1317
    | (have j0 := eq1317 (M.op X0 X0) X1
       grind)
    | exact resolve eq1317 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1990 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq276 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq62 (M.op X0 X0) X0
       grind)
    | exact superpose eq62 eq276
    | (have j0 := eq276 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq276 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1994 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq276 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq276
    | (have j0 := eq276 (τ X0)
       grind)
    | exact resolve eq276 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1996 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq1990 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq1998 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1994 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1994
    | (have j0 := eq1994 X0
       grind)
    | exact resolve eq1994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq2002 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1998 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1998
    | (have j0 := eq1998 X0
       grind)
    | exact resolve eq1998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998
  have eq2017 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2002 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq2002
    | (have j0 := eq2002 (τ X0)
       grind)
    | exact resolve eq2002 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2058 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq41
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2134 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq10
    | (have j1 := eq41 X0 X1
       grind)
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2165 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2058 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2058
    | (have j0 := eq2058 X0 X1
       grind)
    | exact resolve eq2058 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq2839 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2888 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2839 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2839
    | (have j0 := eq2839 X0 X1
       grind)
    | exact resolve eq2839 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839
  have eq4585 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq250
       have i₂ := eq2888 y x
       grind)
    | exact superpose eq2888 eq250
    | (have j1 := eq2888 y x
       grind)
    | (have r₁ := eq250
       have r₂ := eq2888 y x
       grind)
    | exact resolve eq250 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4586 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq250
       have i₂ := eq2165 y x
       grind)
    | exact superpose eq2165 eq250
    | (have j1 := eq2165 (σ y) (σ x)
       grind)
    | (have r₁ := eq250
       have r₂ := eq2165 y x
       grind)
    | exact resolve eq250 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq2165
  have eq4587 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq4586
  have eq4588 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq4585
  have eq5248 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq259 x x
       have i₂ := eq4587
       grind)
    | exact superpose eq4587 eq259
    | exact resolve eq259 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq4587
  have eq5288 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5248
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5248
    | exact resolve eq5248 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5248
  have eq5785 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq143 x
       have i₂ := eq4588
       grind)
    | exact superpose eq4588 eq143
    | exact resolve eq143 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq4588
  have eq5833 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq5785
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5785
    | exact resolve eq5785 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5785
  have eq5834 : x = (k x y) := by grind
  clear eq5833
  have eq12076 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq276 (τ X0)
       have i₂ := eq89 (τ X0) X0
       grind)
    | exact superpose eq89 eq276
    | (have j0 := eq276 (τ X0)
       have j1 := eq89 (τ X0) X0
       grind)
    | exact resolve eq276 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq12119 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq12076 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12076
    | (have j0 := eq12076 X0
       grind)
    | exact resolve eq12076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12076
  have eq12146 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq12119 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12119
    | (have j0 := eq12119 X0
       grind)
    | exact resolve eq12119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12119
  have eq12165 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq12146 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12146
    | (have j0 := eq12146 X0
       grind)
    | exact resolve eq12146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12146
  have eq12181 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12165 X0
       have j1 := eq85 X0 X0
       grind)
    | (have r₁ := eq12165 x
       have r₂ := eq85 x x
       grind)
    | exact resolve eq12165 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12165
  have eq12609 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12181 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12181
    | (have j0 := eq12181 (σ X0)
       grind)
    | exact resolve eq12181 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12181
  have eq12643 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12609 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq12609
    | (have j0 := eq12609 X0
       grind)
    | exact resolve eq12609 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12609
  have eq19250 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq549 X1 X0 (M.op X0 X1) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq19251 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq19250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19250
  have eq19253 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19251 X0 X1
       have i₂ := eq1119 (M.op X0 X1) X1
       grind)
    | (have i₁ := eq19251 X0 X1
       have i₂ := eq1119 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1119 eq19251
    | (have j0 := eq19251 X0 X1
       grind)
    | exact resolve eq19251 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19251
  have eq22378 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1119 (σ X1) (σ X0)
       have i₂ := eq314 X1 X0
       grind)
    | exact superpose eq314 eq1119
    | (have j1 := eq314 X1 X0
       grind)
    | exact resolve eq1119 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq27276 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 X2) ∨ (k (M.op X0 (M.op X1 X1)) X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq620 X2 X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq29122 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 (M.op X0 X1)) = X1 ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq163 X0 X1 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq29123 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq29122 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29122
  have eq29125 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29123 X0 X1
       have i₂ := eq1119 (M.op X0 X1) X1
       grind)
    | (have i₁ := eq29123 X0 X1
       have i₂ := eq1119 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1119 eq29123
    | (have j0 := eq29123 X0 X1
       grind)
    | exact resolve eq29123 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29123
  have eq29374 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2017 (σ X0)
       have i₂ := eq295 (σ X0) X0
       grind)
    | exact superpose eq295 eq2017
    | (have j0 := eq2017 (σ X0)
       have j1 := eq295 (σ X0) X0
       grind)
    | exact resolve eq2017 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq29413 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29374 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29374
    | (have j0 := eq29374 X0
       grind)
    | exact resolve eq29374 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29374
  have eq29433 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29413 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29413
    | (have j0 := eq29413 X0
       grind)
    | exact resolve eq29413 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29413
  have eq29438 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq29433 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29433
    | (have j0 := eq29433 X0
       grind)
    | exact resolve eq29433 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29433
  have eq29441 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq29438 X0
       have j1 := eq85 X0 X0
       grind)
    | (have r₁ := eq29438 x
       have r₂ := eq85 x x
       grind)
    | exact resolve eq29438 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq29438
  have eq30319 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29441 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29441
    | (have j0 := eq29441 (τ X0)
       grind)
    | exact resolve eq29441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29441
  have eq30387 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30319 X0
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq30319
    | (have j0 := eq30319 X0
       grind)
    | exact resolve eq30319 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30319
  have eq52008 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq5288
       grind)
    | exact superpose eq5288 eq9
    | exact resolve eq9 eq5288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5288
  have eq52102 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq52008
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq52008
    | exact resolve eq52008 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52008
  have eq53250 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq52102
       grind)
    | exact superpose eq52102 eq33
    | exact resolve eq33 eq52102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq52102
  have eq53263 : y = (M.op x x) ∨ x = y := by grind
  clear eq53250
  have eq54515 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 y)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq8
    | exact resolve eq8 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54517 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y X0)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X0 X1
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq19
    | exact resolve eq19 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq54529 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 x X1
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq67
    | exact resolve eq67 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq54560 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq497 X1 X0 x
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq497
    | exact resolve eq497 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54580 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op y X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 x X1
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq710
    | exact resolve eq710 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq54582 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1 x
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq956
    | exact resolve eq956 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54583 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 x X1
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq956
    | exact resolve eq956 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq54591 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 y) X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1154 X1 x X0
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq1154
    | exact resolve eq1154 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55630 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (M.op X0 y) (M.op X2 X2)) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1388 X1 (M.op X0 y) X2
       have i₂ := eq54515 X0 (M.op X1 X1)
       grind)
    | exact superpose eq54515 eq1388
    | (have j0 := eq1388 X0 (M.op X0 y) X2
       grind)
    | exact resolve eq1388 eq54515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388 eq54515
  have eq55665 : ∀ X0 X2 : G, (M.op X0 y) = (k (M.op X0 y) (M.op X2 X2)) ∨ x = y := by
    intro X0 X2
    first
    | (have j0 := eq55630 X0 x X2
       grind)
    | (have r₁ := eq55630 X0 x X2
       have r₂ := eq54560 X0 x
       grind)
    | exact resolve eq55630 eq54560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54560 eq55630
  have eq76964 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X1 y) X0) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq54580 (M.op X1 y) X0
       have i₂ := eq54591 (M.op y X0) X1
       grind)
    | exact superpose eq54591 eq54580
    | exact resolve eq54580 eq54591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54580
  have eq76983 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X1 y) X0) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq76964 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76964
  have eq86147 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq55665 X0 x
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq55665
    | exact resolve eq55665 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55665
  have eq86182 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq86147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86147
  have eq92106 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X1 (M.op X2 X2)) ∨ (M.op X3 X0) = (k (M.op X3 (M.op X4 X4)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq497 X2 X1 X3
       have i₂ := eq752 X3 X4 X0
       grind)
    | (have i₁ := eq497 X0 X2 X3
       have i₂ := eq752 X0 X1 (M.op X3 X3)
       grind)
    | exact superpose eq752 eq497
    | (have j1 := eq752 X3 X4 X0
       grind)
    | exact resolve eq497 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq92820 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq2134 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134
  have eq92821 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq92820 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92820
    | (have j0 := eq92820 X0
       grind)
    | exact resolve eq92820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92820
  have eq94787 : (M.op x y) = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq19253 x x
       have i₂ := eq53263
       grind)
    | exact superpose eq53263 eq19253
    | exact resolve eq19253 eq53263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19253 eq53263
  have eq94913 : (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq94787
  have eq108683 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 y) (M.op X1 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1154 y X1 X0
       have i₂ := eq76983 (M.op X1 X1) X0
       grind)
    | exact superpose eq76983 eq1154
    | exact resolve eq1154 eq76983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq76983
  have eq136261 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq22378 y x
       grind)
    | exact superpose eq22378 eq14
    | (have j1 := eq22378 y x
       grind)
    | exact resolve eq14 eq22378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22378
  have eq136433 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq136261
       have i₂ := eq94913
       grind)
    | exact superpose eq94913 eq136261
    | exact resolve eq136261 eq94913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94913
  have eq136434 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq136261
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq136261
    | (have j1 := eq12 y x
       grind)
    | exact resolve eq136261 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136437 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq136261
       have i₂ := eq2888 x y
       grind)
    | exact superpose eq2888 eq136261
    | (have j1 := eq2888 x y
       grind)
    | exact resolve eq136261 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2888 eq136261
  have eq136439 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) := by grind
  clear eq136437
  have eq136440 : y = (M.op x y) ∨ x = y := by grind
  clear eq136433
  have eq136441 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq136439
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq136439
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq136439
    | exact resolve eq136439 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136439
  have eq136442 : y = (k y x) := by grind
  clear eq136441
  have eq136446 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq136434
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq136434
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq136434
    | exact resolve eq136434 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136434
  have eq136447 : y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq136446
  have eq136448 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq136447
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq136447
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq136447
    | exact resolve eq136447 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136447
  have eq136565 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq54529 x X0
       have i₂ := eq136440
       grind)
    | exact superpose eq136440 eq54529
    | exact resolve eq54529 eq136440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54529
  have eq136584 : y = (k y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq86182 x
       have i₂ := eq136440
       grind)
    | exact superpose eq136440 eq86182
    | exact resolve eq86182 eq136440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86182
  have eq136596 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq108683 x x
       have i₂ := eq136440
       grind)
    | exact superpose eq136440 eq108683
    | exact resolve eq108683 eq136440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108683 eq136440
  have eq136645 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq136596 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136596
  have eq136657 : y = (k y y) ∨ x = y := by grind
  clear eq136584
  have eq136676 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq136565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136565
  have eq136722 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq276 y
       have i₂ := eq136657
       grind)
    | exact superpose eq136657 eq276
    | (have j0 := eq276 y
       grind)
    | exact resolve eq276 eq136657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq136730 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ x = y := by
    first
    | (have i₁ := eq2017 y
       have i₂ := eq136657
       grind)
    | exact superpose eq136657 eq2017
    | (have j0 := eq2017 y
       grind)
    | exact resolve eq2017 eq136657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq136742 : y ≠ y ∨ y = (σ (M.op (τ y) (τ y))) ∨ x = y := by
    first
    | (have i₁ := eq92821 y
       have i₂ := eq136657
       grind)
    | exact superpose eq136657 eq92821
    | (have j0 := eq92821 y
       grind)
    | (have r₁ := eq92821 y
       have r₂ := eq136657
       grind)
    | exact resolve eq92821 eq136657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92821 eq136657
  have eq136754 : y = (σ (M.op (τ y) (τ y))) ∨ x = y := by grind
  clear eq136742
  have eq136757 : (τ y) = (M.op (τ y) (τ y)) ∨ x = y := by grind
  clear eq136730
  have eq136760 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq136722
  have eq137445 : y = (M.op y x) ∨ (k x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29125 y y
       have i₂ := eq136448
       grind)
    | exact superpose eq136448 eq29125
    | exact resolve eq29125 eq136448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29125 eq136448
  have eq137448 : y = (M.op x y) ∨ (k x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq137445
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq137445
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq137445
    | exact resolve eq137445 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137445
  have eq137449 : y = (M.op x y) ∨ (k x y) = (M.op y x) := by grind
  clear eq137448
  have eq137481 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq137449
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq137449
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq137449
    | exact resolve eq137449 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137449
  have eq137488 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq137481
       have i₂ := eq5834
       grind)
    | exact superpose eq5834 eq137481
    | exact resolve eq137481 eq5834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5834 eq137481
  have eq137715 : ∀ X0 : G, (M.op y X0) = (M.op X0 x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq54591 X0 x
       have i₂ := eq137488
       grind)
    | exact superpose eq137488 eq54591
    | exact resolve eq54591 eq137488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54591
  have eq137775 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq137488
  have eq137818 : ∀ X0 : G, (M.op y X0) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq137715 X0
       grind)
    | (have r₁ := eq137715 X0
       have r₂ := eq137775
       grind)
    | exact resolve eq137715 eq137775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137715
  have eq141917 : ∀ X0 : G, y = (M.op x (M.op X0 X0)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq136676 (M.op X0 X0)
       have i₂ := eq136645 X0
       grind)
    | exact superpose eq136645 eq136676
    | exact resolve eq136676 eq136645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141970 : ∀ X0 X1 : G, y = (M.op y X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq711 y X0 X0 X1
       have i₂ := eq136645 X0
       grind)
    | exact superpose eq136645 eq711
    | (have j0 := eq711 X0 X1 X0 X1
       grind)
    | exact resolve eq711 eq136645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq142046 : ∀ X0 : G, y = (M.op x (M.op X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq141917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141917
  have eq143826 : (τ (τ y)) ≠ (τ (τ y)) ∨ (τ (τ y)) = (τ (k (τ y) (τ y))) ∨ x = y := by
    first
    | (have i₁ := eq30387 (τ y)
       have i₂ := eq136757
       grind)
    | exact superpose eq136757 eq30387
    | (have j0 := eq30387 (τ y)
       grind)
    | exact resolve eq30387 eq136757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30387
  have eq143832 : ∀ X0 : G, (M.op X0 y) = (M.op (τ y) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq54583 X0 (τ y)
       have i₂ := eq136757
       grind)
    | exact superpose eq136757 eq54583
    | exact resolve eq54583 eq136757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143857 : y = (M.op y (τ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136645 (τ y)
       have i₂ := eq136757
       grind)
    | exact superpose eq136757 eq136645
    | exact resolve eq136645 eq136757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143878 : y = (M.op y (τ y)) ∨ x = y := by grind
  clear eq143857
  have eq143900 : ∀ X0 : G, (M.op X0 y) = (M.op (τ y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq143832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143832
  have eq143906 : (τ (τ y)) = (τ (k (τ y) (τ y))) ∨ x = y := by grind
  clear eq143826
  have eq143923 : (τ (τ (k y y))) = (τ (τ y)) ∨ x = y := by
    first
    | (have i₁ := eq143906
       have i₂ := eq70 y y
       grind)
    | exact superpose eq70 eq143906
    | exact resolve eq143906 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq143906
  have eq144398 : (σ (σ y)) ≠ (σ (σ y)) ∨ (σ (σ y)) = (σ (k (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq12643 (σ y)
       have i₂ := eq136760
       grind)
    | exact superpose eq136760 eq12643
    | (have j0 := eq12643 (σ y)
       grind)
    | exact resolve eq12643 eq136760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12643
  have eq144409 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq54582 X0 (σ y)
       have i₂ := eq136760
       grind)
    | exact superpose eq136760 eq54582
    | exact resolve eq54582 eq136760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54582
  have eq144410 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq54583 X0 (σ y)
       have i₂ := eq136760
       grind)
    | exact superpose eq136760 eq54583
    | exact resolve eq54583 eq136760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54583
  have eq144435 : y = (M.op y (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136645 (σ y)
       have i₂ := eq136760
       grind)
    | exact superpose eq136760 eq136645
    | exact resolve eq136645 eq136760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144456 : y = (M.op y (σ y)) ∨ x = y := by grind
  clear eq144435
  have eq144478 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq144410 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144410
  have eq144479 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq144409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144409
  have eq144485 : (σ (σ y)) = (σ (k (σ y) (σ y))) ∨ x = y := by grind
  clear eq144398
  have eq144504 : (σ (σ y)) = (σ (σ (k y y))) ∨ x = y := by
    first
    | (have i₁ := eq144485
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq144485
    | exact resolve eq144485 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144485
  have eq144811 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 X3) ∨ (M.op X0 X3) = (k (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq27276 x X0 x
       have i₂ := eq497 X0 x X3
       grind)
    | (have i₁ := eq27276 x X3 x
       have i₂ := eq497 X0 x X3
       grind)
    | exact superpose eq497 eq27276
    | (have j0 := eq27276 X0 X1 X3
       grind)
    | (have r₁ := eq27276 x X0 (M.op X3 X3)
       have r₂ := eq497 X0 x X3
       grind)
    | (have r₁ := eq27276 x X3 (M.op X0 X0)
       have r₂ := eq497 X0 x X3
       grind)
    | exact resolve eq27276 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq144826 : ∀ X1 : G, y ≠ (M.op y X1) ∨ (M.op y X1) = (k y X1) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq27276 y x x
       have i₂ := eq136645 x
       grind)
    | exact superpose eq136645 eq27276
    | exact resolve eq27276 eq136645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27276 eq136645
  have eq144838 : ∀ X1 : G, (M.op y X1) = (k y X1) ∨ x = y := by
    intro X1
    first
    | (have j0 := eq144826 X1
       have j1 := eq141970 X1 y
       grind)
    | (have r₁ := eq144826 x
       have r₂ := eq141970 x X1
       grind)
    | exact resolve eq144826 eq141970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141970 eq144826
  have eq144839 : ∀ X0 X1 X3 : G, (M.op X0 X3) = (k (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have j0 := eq144811 X0 X1 X3
       have j1 := eq92106 X3 X1 x X0 X1
       grind)
    | (have r₁ := eq144811 X1 X1 (M.op x x)
       have r₂ := eq92106 (M.op X1 X1) X1 x X3 x
       grind)
    | (have r₁ := eq144811 X1 x X0
       have r₂ := eq92106 X0 X1 x X3 x
       grind)
    | exact resolve eq144811 eq92106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92106 eq144811
  have eq145526 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op y X0) X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq144839 X0 y X1
       have i₂ := eq54517 y X0
       grind)
    | exact superpose eq54517 eq144839
    | exact resolve eq144839 eq54517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54517
  have eq145611 : ∀ X0 : G, (M.op x X0) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq144839 x x X0
       have i₂ := eq142046 x
       grind)
    | exact superpose eq142046 eq144839
    | exact resolve eq144839 eq142046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142046 eq144839
  have eq146567 : (τ y) = (M.op (τ y) y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136757
       have i₂ := eq143900 (τ y)
       grind)
    | exact superpose eq143900 eq136757
    | exact resolve eq136757 eq143900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136757
  have eq146568 : y = (σ (M.op (τ y) y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136754
       have i₂ := eq143900 (τ y)
       grind)
    | exact superpose eq143900 eq136754
    | exact resolve eq136754 eq143900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146571 : y = (k y (σ (M.op (τ y) y))) ∨ x = y := by
    first
    | (have i₁ := eq28 y
       have i₂ := eq143900 (τ y)
       grind)
    | exact superpose eq143900 eq28
    | exact resolve eq28 eq143900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq143900
  have eq146903 : y = (σ (M.op (τ y) y)) ∨ x = y := by grind
  clear eq146568
  have eq146904 : (τ y) = (M.op (τ y) y) ∨ x = y := by grind
  clear eq146567
  have eq147073 : y = (k y (σ (M.op y (τ y)))) ∨ x = y := by
    first
    | (have i₁ := eq146571
       have i₂ := eq1119 (τ y) y
       grind)
    | (have i₁ := eq146571
       have i₂ := eq1119 y (τ y)
       grind)
    | exact superpose eq1119 eq146571
    | exact resolve eq146571 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146571
  have eq147075 : y = (σ (M.op y (τ y))) ∨ x = y := by
    first
    | (have i₁ := eq146903
       have i₂ := eq1119 (τ y) y
       grind)
    | (have i₁ := eq146903
       have i₂ := eq1119 y (τ y)
       grind)
    | exact superpose eq1119 eq146903
    | exact resolve eq146903 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146903
  have eq147076 : (τ y) = (M.op y (τ y)) ∨ x = y := by
    first
    | (have i₁ := eq146904
       have i₂ := eq1119 (τ y) y
       grind)
    | (have i₁ := eq146904
       have i₂ := eq1119 y (τ y)
       grind)
    | exact superpose eq1119 eq146904
    | exact resolve eq146904 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146904
  have eq147155 : y = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147075
       have i₂ := eq143878
       grind)
    | exact superpose eq143878 eq147075
    | exact resolve eq147075 eq143878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147196 : y = (σ y) ∨ x = y := by grind
  clear eq147155
  have eq147200 : (σ (M.op x y)) ≠ (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq147196
       grind)
    | exact superpose eq147196 eq14
    | exact resolve eq14 eq147196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147223 : y = (τ y) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq147196
       grind)
    | exact superpose eq147196 eq9
    | exact resolve eq9 eq147196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147224 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq147196
       grind)
    | exact superpose eq147196 eq13
    | exact resolve eq13 eq147196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147279 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq147200
       have i₂ := eq1119 (σ x) y
       grind)
    | (have i₁ := eq147200
       have i₂ := eq1119 y (σ x)
       grind)
    | exact superpose eq1119 eq147200
    | exact resolve eq147200 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147200
  have eq147290 : y = (σ (M.op y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147075
       have i₂ := eq147223
       grind)
    | exact superpose eq147223 eq147075
    | exact resolve eq147075 eq147223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147075 eq147223
  have eq147319 : y = (σ (M.op y y)) ∨ x = y := by grind
  clear eq147290
  have eq147350 : (M.op y y) = (τ y) ∨ x = y := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq147319
       grind)
    | exact superpose eq147319 eq9
    | exact resolve eq9 eq147319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148327 : (τ y) = (M.op x (τ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136676 (τ y)
       have i₂ := eq147076
       grind)
    | exact superpose eq147076 eq136676
    | exact resolve eq136676 eq147076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136676
  have eq148347 : (τ y) = (M.op x (τ y)) ∨ x = y := by grind
  clear eq148327
  have eq148452 : (τ y) ≠ (τ y) ∨ (τ y) = (k (τ y) x) ∨ x = y := by
    first
    | (have i₁ := eq1317 x (τ y)
       have i₂ := eq148347
       grind)
    | exact superpose eq148347 eq1317
    | (have j0 := eq1317 x (τ y)
       grind)
    | (have r₁ := eq1317 x (τ y)
       have r₂ := eq148347
       grind)
    | exact resolve eq1317 eq148347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317 eq148347
  have eq148456 : (τ y) = (k (τ y) x) ∨ x = y := by grind
  clear eq148452
  have eq148472 : (σ (τ y)) = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16 y x
       have i₂ := eq148456
       grind)
    | exact superpose eq148456 eq16
    | exact resolve eq16 eq148456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq148456
  have eq148482 : y = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq148472
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq148472
    | exact resolve eq148472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148472
  have eq148497 : y = (M.op y (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq144838 (σ x)
       have i₂ := eq148482
       grind)
    | exact superpose eq148482 eq144838
    | exact resolve eq144838 eq148482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144838 eq148482
  have eq148511 : y = (M.op y (σ x)) ∨ x = y := by grind
  clear eq148497
  have eq150436 : (σ y) = (M.op (σ y) y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136760
       have i₂ := eq144478 (σ y)
       grind)
    | exact superpose eq144478 eq136760
    | exact resolve eq136760 eq144478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136760 eq144478
  have eq150767 : (σ y) = (M.op (σ y) y) ∨ x = y := by grind
  clear eq150436
  have eq150940 : (σ y) = (M.op y (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq150767
       have i₂ := eq1119 (σ y) y
       grind)
    | (have i₁ := eq150767
       have i₂ := eq1119 y (σ y)
       grind)
    | exact superpose eq1119 eq150767
    | exact resolve eq150767 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150767
  have eq151682 : (σ y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq150940
       have i₂ := eq144479 y
       grind)
    | exact superpose eq144479 eq150940
    | exact resolve eq150940 eq144479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144479 eq150940
  have eq151766 : (σ y) = (M.op y y) ∨ x = y := by grind
  clear eq151682
  have eq151954 : (σ y) = (τ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147350
       have i₂ := eq151766
       grind)
    | exact superpose eq151766 eq147350
    | exact resolve eq147350 eq151766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147350 eq151766
  have eq152260 : (σ y) = (τ y) ∨ x = y := by grind
  clear eq151954
  have eq152370 : y = (σ (M.op (σ y) (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq136754
       have i₂ := eq152260
       grind)
    | exact superpose eq152260 eq136754
    | exact resolve eq136754 eq152260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136754 eq152260
  have eq152430 : y = (σ (M.op (σ y) (σ y))) ∨ x = y := by grind
  clear eq152370
  have eq167630 : (τ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (M.op (σ y) (σ y))
       have i₂ := eq152430
       grind)
    | exact superpose eq152430 eq9
    | exact resolve eq9 eq152430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169524 : y = (σ (M.op y x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq147319
       have i₂ := eq137818 y
       grind)
    | exact superpose eq137818 eq147319
    | exact resolve eq147319 eq137818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147319
  have eq169890 : y = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq169524
       have r₂ := eq137775
       grind)
    | exact resolve eq169524 eq137775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169524
  have eq170066 : y = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq169890
       have i₂ := eq1119 y x
       grind)
    | (have i₁ := eq169890
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq169890
    | exact resolve eq169890 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169890
  have eq173278 : ∀ X0 : G, (M.op (σ x) X0) = (k y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq145526 (σ x) X0
       have i₂ := eq148511
       grind)
    | exact superpose eq148511 eq145526
    | exact resolve eq145526 eq148511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148511
  have eq173283 : ∀ X0 : G, (M.op (σ y) X0) = (k y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq145526 (σ y) X0
       have i₂ := eq144456
       grind)
    | exact superpose eq144456 eq145526
    | exact resolve eq145526 eq144456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144456
  have eq173292 : ∀ X0 : G, (k (τ y) X0) = (M.op (τ y) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq145526 (τ y) X0
       have i₂ := eq147076
       grind)
    | exact superpose eq147076 eq145526
    | exact resolve eq145526 eq147076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147076
  have eq173293 : ∀ X0 : G, (k y X0) = (M.op (τ y) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq145526 (τ y) X0
       have i₂ := eq143878
       grind)
    | exact superpose eq143878 eq145526
    | exact resolve eq145526 eq143878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143878 eq145526
  have eq173461 : ∀ X0 : G, (k y X0) = (M.op (τ y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq173293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173293
  have eq173462 : ∀ X0 : G, (k (τ y) X0) = (M.op (τ y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq173292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173292
  have eq173471 : ∀ X0 : G, (M.op (σ y) X0) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq173283 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173283
  have eq173476 : ∀ X0 : G, (M.op (σ x) X0) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq173278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173278
  have eq173684 : ∀ X0 : G, (k y X0) = (M.op X0 (τ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1119 X0 (τ y)
       have i₂ := eq173461 X0
       grind)
    | exact superpose eq173461 eq1119
    | exact resolve eq1119 eq173461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173461
  have eq174876 : (τ y) = (k y (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq167630
       have i₂ := eq173471 (σ y)
       grind)
    | exact superpose eq173471 eq167630
    | exact resolve eq167630 eq173471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167630
  have eq174877 : y = (σ (k y (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq152430
       have i₂ := eq173471 (σ y)
       grind)
    | exact superpose eq173471 eq152430
    | exact resolve eq152430 eq173471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152430 eq173471
  have eq175200 : y = (σ (k y (σ y))) ∨ x = y := by grind
  clear eq174877
  have eq175201 : (τ y) = (k y (σ y)) ∨ x = y := by grind
  clear eq174876
  have eq175303 : y = (σ (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq175200
       have i₂ := eq147196
       grind)
    | exact superpose eq147196 eq175200
    | exact resolve eq175200 eq147196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147196 eq175200
  have eq175334 : y = (σ (k y y)) ∨ x = y := by grind
  clear eq175303
  have eq175366 : (k y y) = (τ y) ∨ x = y := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq175334
       grind)
    | exact superpose eq175334 eq9
    | exact resolve eq9 eq175334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175334
  have eq175492 : (τ (τ y)) = (k (τ y) y) ∨ x = y := by
    first
    | (have i₁ := eq27 y y
       have i₂ := eq175201
       grind)
    | exact superpose eq175201 eq27
    | exact resolve eq27 eq175201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq175201
  have eq179327 : ∀ X0 : G, (M.op X0 (σ x)) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1119 X0 (σ x)
       have i₂ := eq173476 X0
       grind)
    | exact superpose eq173476 eq1119
    | exact resolve eq1119 eq173476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179410 : (k y x) = (M.op y (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq137818 (σ x)
       have i₂ := eq173476 x
       grind)
    | exact superpose eq173476 eq137818
    | exact resolve eq137818 eq173476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137818 eq173476
  have eq179626 : (k y x) = (M.op y (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq179410
       have r₂ := eq137775
       grind)
    | exact resolve eq179410 eq137775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179410
  have eq179668 : y = (M.op y (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq179626
       have i₂ := eq136442
       grind)
    | exact superpose eq136442 eq179626
    | exact resolve eq179626 eq136442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136442 eq179626
  have eq215538 : (τ (τ y)) = (τ (τ (τ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq143923
       have i₂ := eq175366
       grind)
    | exact superpose eq175366 eq143923
    | exact resolve eq143923 eq175366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143923 eq175366
  have eq215561 : (τ (τ y)) = (τ (τ (τ y))) ∨ x = y := by grind
  clear eq215538
  have eq225677 : y = (k y (σ (k y y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147073
       have i₂ := eq173684 y
       grind)
    | exact superpose eq173684 eq147073
    | exact resolve eq147073 eq173684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147073
  have eq225705 : y = (k y (σ (k y y))) ∨ x = y := by grind
  clear eq225677
  have eq239185 : (τ (τ y)) = (M.op (τ y) y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq175492
       have i₂ := eq173462 y
       grind)
    | exact superpose eq173462 eq175492
    | exact resolve eq175492 eq173462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173462 eq175492
  have eq239201 : (τ (τ y)) = (M.op (τ y) y) ∨ x = y := by grind
  clear eq239185
  have eq239227 : (τ (τ y)) = (M.op y (τ y)) ∨ x = y := by
    first
    | (have i₁ := eq239201
       have i₂ := eq1119 (τ y) y
       grind)
    | (have i₁ := eq239201
       have i₂ := eq1119 y (τ y)
       grind)
    | exact superpose eq1119 eq239201
    | exact resolve eq239201 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq239201
  have eq239587 : (k y y) = (τ (τ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq173684 y
       have i₂ := eq239227
       grind)
    | exact superpose eq239227 eq173684
    | exact resolve eq173684 eq239227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173684 eq239227
  have eq239598 : (k y y) = (τ (τ y)) ∨ x = y := by grind
  clear eq239587
  have eq239676 : (k y y) = (τ (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq215561
       have i₂ := eq239598
       grind)
    | exact superpose eq239598 eq215561
    | exact resolve eq215561 eq239598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215561
  have eq239686 : (k y y) = (τ (k y y)) ∨ x = y := by grind
  clear eq239676
  have eq240053 : (k y y) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq239686
       grind)
    | exact superpose eq239686 eq10
    | exact resolve eq10 eq239686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239686
  have eq240294 : (σ (k y y)) = (σ (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq144504
       have i₂ := eq240053
       grind)
    | exact superpose eq240053 eq144504
    | exact resolve eq144504 eq240053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144504
  have eq240314 : (σ (k y y)) = (σ (σ y)) ∨ x = y := by grind
  clear eq240294
  have eq240565 : (k y y) = (σ (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq240053
       have i₂ := eq240314
       grind)
    | exact superpose eq240314 eq240053
    | exact resolve eq240053 eq240314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240053 eq240314
  have eq240575 : (k y y) = (σ (σ y)) ∨ x = y := by grind
  clear eq240565
  have eq243825 : y = (σ (k y (k y y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq225705
       have i₂ := eq147224 (k y y)
       grind)
    | exact superpose eq147224 eq225705
    | exact resolve eq225705 eq147224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225705
  have eq243874 : y = (σ (k y (k y y))) ∨ x = y := by grind
  clear eq243825
  have eq244203 : (τ y) = (k y (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (k y (k y y))
       have i₂ := eq243874
       grind)
    | exact superpose eq243874 eq9
    | exact resolve eq9 eq243874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243874
  have eq244543 : (τ y) = (k y (σ (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq244203
       have i₂ := eq240575
       grind)
    | exact superpose eq240575 eq244203
    | exact resolve eq244203 eq240575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240575 eq244203
  have eq244633 : (τ y) = (k y (σ (σ y))) ∨ x = y := by grind
  clear eq244543
  have eq248098 : (τ y) = (σ (k y (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147224 (σ y)
       have i₂ := eq244633
       grind)
    | exact superpose eq244633 eq147224
    | exact resolve eq147224 eq244633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244633
  have eq248142 : (τ y) = (σ (k y (σ y))) ∨ x = y := by grind
  clear eq248098
  have eq248631 : (k y (σ y)) = (τ (τ y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (k y (σ y))
       have i₂ := eq248142
       grind)
    | exact superpose eq248142 eq9
    | exact resolve eq9 eq248142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248142
  have eq248810 : (σ (k y y)) = (τ (τ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147224 y
       have i₂ := eq248631
       grind)
    | exact superpose eq248631 eq147224
    | exact resolve eq147224 eq248631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147224 eq248631
  have eq248854 : (σ (k y y)) = (τ (τ y)) ∨ x = y := by grind
  clear eq248810
  have eq249297 : (σ (M.op x y)) = (τ (τ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq248854
       have i₂ := eq145611 y
       grind)
    | exact superpose eq145611 eq248854
    | exact resolve eq248854 eq145611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145611 eq248854
  have eq249362 : (σ (M.op x y)) = (τ (τ y)) ∨ x = y := by grind
  clear eq249297
  have eq250126 : (M.op x y) = (τ (τ (τ y))) ∨ x = y := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq249362
       grind)
    | exact superpose eq249362 eq9
    | exact resolve eq9 eq249362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249362
  have eq250420 : (M.op x y) = (τ (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq250126
       have i₂ := eq239598
       grind)
    | exact superpose eq239598 eq250126
    | exact resolve eq250126 eq239598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239598 eq250126
  have eq250446 : (M.op x y) = (τ (k y y)) ∨ x = y := by grind
  clear eq250420
  have eq250667 : (σ (M.op x y)) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq250446
       grind)
    | exact superpose eq250446 eq10
    | exact resolve eq10 eq250446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250446
  have eq256762 : y ≠ (M.op y (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq147279
       have i₂ := eq170066
       grind)
    | exact superpose eq170066 eq147279
    | exact resolve eq147279 eq170066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170066
  have eq256770 : (k y y) ≠ (M.op y (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq147279
       have i₂ := eq250667
       grind)
    | exact superpose eq250667 eq147279
    | exact resolve eq147279 eq250667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147279 eq250667
  have eq256771 : (k y y) ≠ (M.op y (σ x)) ∨ x = y := by grind
  clear eq256770
  have eq256785 : x = y := by
    first
    | (have r₁ := eq256771
       have r₂ := eq179327 y
       grind)
    | exact resolve eq256771 eq179327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179327 eq256771
  have eq256790 : y ≠ (M.op y (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq256762
       have r₂ := eq137775
       grind)
    | exact resolve eq256762 eq137775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137775 eq256762
  have eq256795 : x = (M.op x y) := by
    first
    | (have r₁ := eq256790
       have r₂ := eq179668
       grind)
    | exact resolve eq256790 eq179668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179668 eq256790
  have eq256797 : x = (M.op x x) := by
    first
    | (have i₁ := eq256795
       have i₂ := eq256785
       grind)
    | exact superpose eq256785 eq256795
    | exact resolve eq256795 eq256785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256795
  have eq256798 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq256785
       grind)
    | exact superpose eq256785 eq14
    | exact resolve eq14 eq256785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256785
  have eq256929 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq256798
       have i₂ := eq256797
       grind)
    | exact superpose eq256797 eq256798
    | exact resolve eq256798 eq256797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256798
  have eq257051 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq1996 x
       have i₂ := eq256797
       grind)
    | exact superpose eq256797 eq1996
    | exact resolve eq1996 eq256797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq257181 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq257051
       have i₂ := eq256797
       grind)
    | exact superpose eq256797 eq257051
    | exact resolve eq257051 eq256797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256797 eq257051
  have eq257191 : False := by grind
  exact eq257191

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3352 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq89 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq93 (σ X0) (σ X1)
       grind)
    | exact superpose eq93 eq13
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq109
    | exact resolve eq109 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq109
  have eq1299 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq116 x y
       grind)
    | exact superpose eq116 eq14
    | (have r₁ := eq14
       have r₂ := eq116 x y
       grind)
    | exact resolve eq14 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1322 : False := by grind
  exact eq1322

/-- `Equation3364`: `x ◇ y = y ◇ (z ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3364 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3364 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3364.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 (M.op X0 X2))) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op X0 X1)
       have i₂ := eq8 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    grind
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X1 (M.op X0 X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq20
    | exact resolve eq20 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq23 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq32 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq39 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 X2)) X3) = (M.op X3 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op X2 (M.op X0 X2)) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X1 (M.op X0 X1))) = (M.op (M.op X2 (M.op X2 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op X2 (M.op X2 X0)) X3
       have i₂ := eq19 X2 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X1
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X1 X0) X2
       have i₂ := eq19 X1 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    grind
  have eq57 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq19 X1 X0 X0
       grind)
    | exact superpose eq19 eq55
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq60 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X2 (M.op X2 X0)) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq48 X0 x X2 X3
       have i₂ := eq8 X0 X3 x
       grind)
    | exact superpose eq8 eq48
    | exact resolve eq48 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X2 (M.op X0 X2)) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq47 X0 x X2 X3
       have i₂ := eq8 X0 X3 x
       grind)
    | exact superpose eq8 eq47
    | exact resolve eq47 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq62 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq31 (τ X1) X0
       grind)
    | exact superpose eq31 eq17
    | (have j1 := eq31 (τ X1) X0
       grind)
    | exact resolve eq17 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq167 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq153 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq153
    | exact resolve eq153 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq216 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq32 X0 X1 X0
       grind)
    | exact superpose eq32 eq21
    | (have j1 := eq32 X1 X0 x
       grind)
    | exact resolve eq21 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq330 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34 x y
       grind)
    | exact superpose eq34 eq14
    | (have j1 := eq34 x y
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq167
    | (have j1 := eq34 X1 X0
       grind)
    | exact resolve eq167 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq352
    | (have j0 := eq352 X0 X1
       grind)
    | exact resolve eq352 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq584 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X0 X1 X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq50 X0 X1 (M.op X1 X0)
       have i₂ := eq51 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X2 X1 X0
       have i₂ := eq51 X1 X2 X0
       grind)
    | (have i₁ := eq50 X0 X1 (M.op X0 X1)
       have i₂ := eq51 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq707 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X2 (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X3 (M.op X3 X0)) X1
       have i₂ := eq60 X0 X3 (M.op X1 (M.op X2 X1))
       grind)
    | exact superpose eq60 eq8
    | exact resolve eq8 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X2 (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 X0 (M.op X1 (M.op X1 X2))
       have i₂ := eq60 X2 X1 (M.op X3 (M.op X3 X0))
       grind)
    | exact superpose eq60 eq19
    | exact resolve eq19 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq718 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq708 X0 X1 X2 x
       have i₂ := eq19 x X0 X2
       grind)
    | exact superpose eq19 eq708
    | exact resolve eq708 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq719 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq707 X0 X1 X2 x
       have i₂ := eq19 x X0 X2
       grind)
    | exact superpose eq19 eq707
    | exact resolve eq707 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq1324 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X0 X1
       have i₂ := eq718 X1 x X0
       grind)
    | exact superpose eq718 eq19
    | exact resolve eq19 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1361 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op X1 (M.op X3 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X1 X0 (M.op X3 (M.op X3 X2))
       have i₂ := eq718 (M.op X0 (M.op X1 X0)) X3 X2
       grind)
    | exact superpose eq718 eq61
    | exact resolve eq61 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq718
  have eq1362 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1361 X0 X1 X2 x
       have i₂ := eq19 x X2 X1
       grind)
    | exact superpose eq19 eq1361
    | exact resolve eq1361 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq1549 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1 X0
       have i₂ := eq1324 X1 X0
       grind)
    | (have i₁ := eq77 X1 X0
       have i₂ := eq1324 X0 X1
       grind)
    | exact superpose eq1324 eq77
    | (have j0 := eq77 X1 X0
       grind)
    | exact resolve eq77 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2242 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2310 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq10
    | (have j1 := eq39 X0 X1
       grind)
    | exact resolve eq10 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2345 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2242 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2242
    | (have j0 := eq2242 X0 X1
       grind)
    | exact resolve eq2242 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq2637 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2654 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq74 (τ X0) X0
       grind)
    | exact superpose eq74 eq27
    | (have j1 := eq74 (τ X0) X0
       grind)
    | exact resolve eq27 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq74
  have eq2678 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2654 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2654
    | (have j0 := eq2654 X0
       grind)
    | exact resolve eq2654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654
  have eq2684 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2637 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2637
    | (have j0 := eq2637 X0 X1
       grind)
    | exact resolve eq2637 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq2685 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2678 X0
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq2678
    | (have j0 := eq2678 X0
       grind)
    | exact resolve eq2678 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2678
  have eq4367 : ∀ X0 X1 : G, (σ X0) = (k (σ (τ X1)) X1) ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (τ X0) X0
       have i₂ := eq35 X0 X1
       grind)
    | (have i₁ := eq39 X0 X1
       have i₂ := eq35 X0 (M.op X0 (τ X1))
       grind)
    | exact superpose eq35 eq39
    | (have j1 := eq35 X1 X0
       grind)
    | exact resolve eq39 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq39
  have eq4415 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (σ X0) = (k X1 X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4367 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4367
    | (have j0 := eq4367 X0 X1
       grind)
    | exact resolve eq4367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4367
  have eq5020 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq330
       have i₂ := eq31 y x
       grind)
    | exact superpose eq31 eq330
    | (have j1 := eq31 y x
       grind)
    | exact resolve eq330 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq5022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq330
       have i₂ := eq2345 y x
       grind)
    | exact superpose eq2345 eq330
    | (have j1 := eq2345 (σ y) (σ x)
       grind)
    | (have r₁ := eq330
       have r₂ := eq2345 y x
       grind)
    | exact resolve eq330 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq2345
  have eq5023 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq5022
  have eq5025 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq5020
  have eq5034 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq5025
       grind)
    | exact superpose eq5025 eq167
    | exact resolve eq167 eq5025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq5025
  have eq5079 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq5034
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5034
    | exact resolve eq5034 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5034
  have eq5080 : x = (k x y) := by grind
  clear eq5079
  have eq5165 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq5080
       grind)
    | exact superpose eq5080 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq5080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5080
  have eq5186 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq216 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq216
    | (have j0 := eq216 X1 X0
       have j1 := eq12 X1 X0
       grind)
    | exact resolve eq216 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq5343 : ∀ X0 : G, (M.op X0 (M.op y x)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq719 X0 y x
       have i₂ := eq5165
       grind)
    | exact superpose eq5165 eq719
    | exact resolve eq719 eq5165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5165
  have eq5350 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5343 X0
       have i₂ := eq603 X0 y x
       grind)
    | (have i₁ := eq5343 X0
       have i₂ := eq603 X0 x y
       grind)
    | exact superpose eq603 eq5343
    | exact resolve eq5343 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5343
  have eq6293 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X0
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq342
    | (have j0 := eq342 X1 X0
       have j1 := eq34 X1 X0
       grind)
    | exact resolve eq342 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6376 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6293 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6293
    | (have j0 := eq6293 X0 X1
       grind)
    | exact resolve eq6293 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6293
  have eq6954 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq342 x x
       have i₂ := eq5023
       grind)
    | exact superpose eq5023 eq342
    | exact resolve eq342 eq5023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5023
  have eq7005 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6954
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6954
    | exact resolve eq6954 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6954
  have eq8025 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq44 X0 (k (σ X0) (σ X0))
       have i₂ := eq2685 (σ X0)
       grind)
    | exact superpose eq2685 eq44
    | (have j1 := eq2685 (σ X0)
       grind)
    | exact resolve eq44 eq2685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq8028 : ∀ X0 : G, (τ (σ X0)) = (k X0 (k (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8025 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq8025
    | (have j0 := eq8025 X0
       grind)
    | exact resolve eq8025 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8025
  have eq8045 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8028 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq8028
    | (have j0 := eq8028 X0
       grind)
    | exact resolve eq8028 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8028
  have eq8054 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8045 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq8045
    | (have j0 := eq8045 X0
       grind)
    | exact resolve eq8045 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8045
  have eq8062 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8054 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq8054
    | (have j0 := eq8054 X0
       grind)
    | exact resolve eq8054 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8054
  have eq52513 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1324 (σ X1) (σ X0)
       have i₂ := eq368 X1 X0
       grind)
    | exact superpose eq368 eq1324
    | (have j1 := eq368 X1 X0
       grind)
    | exact resolve eq1324 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq74668 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq2310 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq74669 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq74668 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74668
    | (have j0 := eq74668 X0
       grind)
    | exact resolve eq74668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74668
  have eq74851 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq74669 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq74669
    | (have j0 := eq74669 (σ X0)
       grind)
    | exact resolve eq74669 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74669
  have eq74869 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74851 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74851
    | (have j0 := eq74851 X0
       grind)
    | exact resolve eq74851 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74851
  have eq83830 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq9
    | exact resolve eq9 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005
  have eq83841 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83830
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq83830
    | exact resolve eq83830 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83830
  have eq83938 : y = (M.op x x) ∨ x = y ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5186 x x
       have i₂ := eq83841
       grind)
    | exact superpose eq83841 eq5186
    | exact resolve eq5186 eq83841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186 eq83841
  have eq83948 : y = (M.op x x) ∨ x = y := by grind
  clear eq83938
  have eq83995 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19 x x X0
       have i₂ := eq83948
       grind)
    | exact superpose eq83948 eq19
    | exact resolve eq19 eq83948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq84004 : (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq83948
       grind)
    | exact superpose eq83948 eq57
    | exact resolve eq57 eq83948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84084 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1362 x x X0
       have i₂ := eq83948
       grind)
    | exact superpose eq83948 eq1362
    | exact resolve eq1362 eq83948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84866 : (M.op x y) = (k (M.op x y) (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq21 x y
       have i₂ := eq83995 y
       grind)
    | exact superpose eq83995 eq21
    | exact resolve eq21 eq83995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq84920 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq77 X0 (M.op x y)
       have i₂ := eq83995 X0
       grind)
    | exact superpose eq83995 eq77
    | (have j0 := eq77 X0 (M.op x y)
       grind)
    | exact resolve eq77 eq83995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq90226 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52513 y x
       grind)
    | exact superpose eq52513 eq14
    | (have j1 := eq52513 y x
       grind)
    | exact resolve eq14 eq52513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52513
  have eq90418 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90226
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq90226
    | (have j1 := eq12 y x
       grind)
    | exact resolve eq90226 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90422 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq90226
       have i₂ := eq2684 x y
       grind)
    | exact superpose eq2684 eq90226
    | (have j1 := eq2684 x y
       grind)
    | exact resolve eq90226 eq2684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90226
  have eq90424 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) := by grind
  clear eq90422
  have eq90425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq90424
       have i₂ := eq1324 y x
       grind)
    | (have i₁ := eq90424
       have i₂ := eq1324 x y
       grind)
    | exact superpose eq1324 eq90424
    | exact resolve eq90424 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90424
  have eq90426 : y = (k y x) := by grind
  clear eq90425
  have eq90430 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90418
       have i₂ := eq1324 y x
       grind)
    | (have i₁ := eq90418
       have i₂ := eq1324 x y
       grind)
    | exact superpose eq1324 eq90418
    | exact resolve eq90418 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90418
  have eq90431 : y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq90430
  have eq90432 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90431
       have i₂ := eq1324 y x
       grind)
    | (have i₁ := eq90431
       have i₂ := eq1324 x y
       grind)
    | exact superpose eq1324 eq90431
    | exact resolve eq90431 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90431
  have eq90687 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq719 X0 y y
       have i₂ := eq90432
       grind)
    | exact superpose eq90432 eq719
    | exact resolve eq719 eq90432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq90715 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1362 y y X0
       have i₂ := eq90432
       grind)
    | exact superpose eq90432 eq1362
    | exact resolve eq1362 eq90432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90716 : x ≠ y ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1549 y y
       have i₂ := eq90432
       grind)
    | exact superpose eq90432 eq1549
    | (have j0 := eq1549 y y
       grind)
    | (have r₁ := eq1549 x y
       have r₂ := eq90432
       grind)
    | exact resolve eq1549 eq90432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549 eq90432
  have eq90735 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90715 X0
       have i₂ := eq584 y x X0
       grind)
    | (have i₁ := eq90715 X0
       have i₂ := eq584 x y X0
       grind)
    | exact superpose eq584 eq90715
    | exact resolve eq90715 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq90715
  have eq90740 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90687 X0
       have i₂ := eq603 X0 y x
       grind)
    | (have i₁ := eq90687 X0
       have i₂ := eq603 X0 x y
       grind)
    | exact superpose eq603 eq90687
    | exact resolve eq90687 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq90687
  have eq90980 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq84084 X0
       have i₂ := eq90735 X0
       grind)
    | exact superpose eq90735 eq84084
    | exact resolve eq84084 eq90735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84084 eq90735
  have eq91483 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op y y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1362 y x X0
       have i₂ := eq90740 y
       grind)
    | exact superpose eq90740 eq1362
    | exact resolve eq1362 eq90740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362 eq90740
  have eq103927 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4415 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4415
    | (have j0 := eq4415 X1 (σ X0)
       grind)
    | exact resolve eq4415 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4415
  have eq103936 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq103927 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq103927
    | (have j0 := eq103927 X0 X1
       grind)
    | exact resolve eq103927 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103927
  have eq103937 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq103936 X0 X1
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq103936
    | (have j0 := eq103936 X0 X1
       grind)
    | exact resolve eq103936 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103936
  have eq103988 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq6376 y x
       grind)
    | exact superpose eq6376 eq14
    | (have j1 := eq6376 y x
       grind)
    | (have r₁ := eq14
       have r₂ := eq6376 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq6376 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq6376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6376
  have eq103997 : (σ y) = (σ (k x x)) ∨ x = y := by
    first
    | (have j1 := eq103937 x y
       grind)
    | (have r₁ := eq103988
       have r₂ := eq103937 x y
       grind)
    | (have r₁ := eq103988
       have r₂ := eq103937 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq103988
       have r₂ := eq103937 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq103988 eq103937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103937 eq103988
  have eq104032 : (k x x) = (τ (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq103997
       grind)
    | exact superpose eq103997 eq9
    | exact resolve eq9 eq103997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103997
  have eq104089 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq104032
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq104032
    | exact resolve eq104032 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104032
  have eq104173 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq2684 x x
       have i₂ := eq104089
       grind)
    | exact superpose eq104089 eq2684
    | exact resolve eq2684 eq104089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684 eq104089
  have eq104188 : (σ y) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq104173
  have eq104260 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op x x)
       have i₂ := eq104188
       grind)
    | exact superpose eq104188 eq13
    | exact resolve eq13 eq104188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104188
  have eq104310 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq104260 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq104260
    | exact resolve eq104260 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104260
  have eq106706 : (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq104310 (M.op x y)
       have i₂ := eq84866
       grind)
    | exact superpose eq84866 eq104310
    | exact resolve eq104310 eq84866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84866 eq104310
  have eq106734 : (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ x = y := by grind
  clear eq106706
  have eq110897 : y ≠ (M.op x x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq90980
  have eq110947 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq110897
       have r₂ := eq83948
       grind)
    | exact resolve eq110897 eq83948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83948 eq110897
  have eq111049 : ∀ X0 : G, (M.op X0 y) = (M.op x X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq83995 X0
       have i₂ := eq110947
       grind)
    | exact superpose eq110947 eq83995
    | exact resolve eq83995 eq110947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83995
  have eq111069 : (σ y) = (σ (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq106734
       have i₂ := eq110947
       grind)
    | exact superpose eq110947 eq106734
    | exact resolve eq106734 eq110947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106734
  have eq111071 : y ≠ y ∨ y = (k y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq84920 y
       have i₂ := eq110947
       grind)
    | exact superpose eq110947 eq84920
    | (have r₁ := eq84920 y
       have r₂ := eq110947
       grind)
    | exact resolve eq84920 eq110947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84920 eq110947
  have eq111282 : y ≠ y ∨ y = (k y y) ∨ x = y := by grind
  clear eq111071
  have eq111283 : y = (k y y) ∨ x = y := by grind
  clear eq111282
  have eq111285 : (σ y) = (σ (k y y)) ∨ x = y := by grind
  clear eq111069
  have eq111295 : ∀ X0 : G, (M.op X0 y) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq111049 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111049
  have eq111519 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq74869 y
       have i₂ := eq111283
       grind)
    | exact superpose eq111283 eq74869
    | (have j0 := eq74869 y
       grind)
    | exact resolve eq74869 eq111283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74869 eq111283
  have eq111535 : (σ y) = (σ (M.op y y)) ∨ x = y := by grind
  clear eq111519
  have eq112102 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (k y y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq26 X0 (k y y)
       have i₂ := eq111285
       grind)
    | exact superpose eq111285 eq26
    | exact resolve eq26 eq111285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111285
  have eq112155 : ∀ X0 : G, (k (τ X0) y) = (k (τ X0) (k y y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq112102 X0
       have i₂ := eq26 X0 y
       grind)
    | exact superpose eq26 eq112102
    | exact resolve eq112102 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq112102
  have eq114330 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq111535
       have i₂ := eq111295 y
       grind)
    | exact superpose eq111295 eq111535
    | exact resolve eq111535 eq111295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114352 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (M.op y y) (τ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq44 (M.op y y) X0
       have i₂ := eq111535
       grind)
    | exact superpose eq111535 eq44
    | exact resolve eq44 eq111535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111535
  have eq114375 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq114330
  have eq114383 : ∀ X0 : G, (k y (τ X0)) = (k (M.op y y) (τ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq114352 X0
       have i₂ := eq44 y X0
       grind)
    | exact superpose eq44 eq114352
    | exact resolve eq114352 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq114352
  have eq143471 : ∀ X0 : G, (k X0 y) = (k X0 (k y y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq112155 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112155
    | exact resolve eq112155 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112155
  have eq167176 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq114383 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq114383
    | exact resolve eq114383 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114383
  have eq167233 : ∀ X0 : G, (k (M.op x y) X0) = (k y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq167176 X0
       have i₂ := eq111295 y
       grind)
    | exact superpose eq111295 eq167176
    | exact resolve eq167176 eq111295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111295 eq167176
  have eq167326 : ∀ X0 : G, (k (M.op x y) X0) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq167233 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167233
  have eq167749 : (k (M.op x y) y) = (k y (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq143471 (M.op x y)
       have i₂ := eq167326 (k y y)
       grind)
    | exact superpose eq167326 eq143471
    | exact resolve eq143471 eq167326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143471 eq167326
  have eq167750 : (k (M.op x y) y) = (k y (k y y)) ∨ x = y := by grind
  clear eq167749
  have eq203436 : (M.op x y) = (k y (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq84004
       have i₂ := eq167750
       grind)
    | exact superpose eq167750 eq84004
    | exact resolve eq84004 eq167750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84004 eq167750
  have eq203455 : (M.op x y) = (k y (k y y)) ∨ x = y := by grind
  clear eq203436
  have eq203512 : y = (M.op x y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq8062 y
       have i₂ := eq203455
       grind)
    | exact superpose eq203455 eq8062
    | (have j0 := eq8062 y
       grind)
    | exact resolve eq8062 eq203455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8062 eq203455
  have eq203542 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq203512
       have r₂ := eq90716
       grind)
    | exact resolve eq203512 eq90716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90716 eq203512
  have eq203602 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq203542
       grind)
    | exact superpose eq203542 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq203542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203542
  have eq203606 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq203602
  have eq203657 : ∀ X0 : G, (M.op y X0) = (M.op X0 x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq91483 X0
       have i₂ := eq203606
       grind)
    | exact superpose eq203606 eq91483
    | exact resolve eq91483 eq203606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91483
  have eq203910 : ∀ X0 : G, (M.op y X0) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq203657 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203657
  have eq204086 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq203606
       have i₂ := eq203910 y
       grind)
    | exact superpose eq203910 eq203606
    | exact resolve eq203606 eq203910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203606 eq203910
  have eq204161 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq204086
  have eq204182 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq204161
       have i₂ := eq1324 y x
       grind)
    | (have i₁ := eq204161
       have i₂ := eq1324 x y
       grind)
    | exact superpose eq1324 eq204161
    | exact resolve eq204161 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204161
  have eq204183 : y = (M.op x y) := by grind
  clear eq204182
  have eq204207 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5350 X0
       have i₂ := eq204183
       grind)
    | exact superpose eq204183 eq5350
    | exact resolve eq5350 eq204183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350
  have eq213041 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq204183
       have i₂ := eq204207 x
       grind)
    | exact superpose eq204207 eq204183
    | exact resolve eq204183 eq204207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204207
  have eq213189 : y = (M.op x x) := by grind
  clear eq213041
  have eq213445 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq213189
       grind)
    | exact superpose eq213189 eq57
    | exact resolve eq57 eq213189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq213720 : y = (k y y) := by
    first
    | (have i₁ := eq213445
       have i₂ := eq204183
       grind)
    | exact superpose eq204183 eq213445
    | exact resolve eq213445 eq204183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204183 eq213445
  have eq213826 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq363 y
       have i₂ := eq213720
       grind)
    | exact superpose eq213720 eq363
    | (have j0 := eq363 y
       grind)
    | exact resolve eq363 eq213720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq213720
  have eq213866 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq213826
  have eq219241 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq342 y X0
       have i₂ := eq213866
       grind)
    | exact superpose eq213866 eq342
    | (have j0 := eq342 y X0
       grind)
    | exact resolve eq342 eq213866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq219395 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq219241 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq219241
    | (have j0 := eq219241 X0
       grind)
    | exact resolve eq219241 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219241
  have eq230691 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq1324 (σ X0) (σ y)
       have i₂ := eq219395 X0
       grind)
    | exact superpose eq219395 eq1324
    | (have j1 := eq219395 X0
       grind)
    | exact resolve eq1324 eq219395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324 eq219395
  have eq230770 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq230691 x
       grind)
    | exact superpose eq230691 eq14
    | (have j1 := eq230691 x
       grind)
    | exact resolve eq14 eq230691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230691
  have eq230794 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq230770
       have i₂ := eq90426
       grind)
    | exact superpose eq90426 eq230770
    | exact resolve eq230770 eq90426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90426 eq230770
  have eq230797 : x = y := by
    first
    | (have r₁ := eq230794
       have r₂ := eq114375
       grind)
    | exact resolve eq230794 eq114375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114375 eq230794
  have eq230798 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq230797
       grind)
    | exact superpose eq230797 eq14
    | exact resolve eq14 eq230797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231009 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq213866
       have i₂ := eq230797
       grind)
    | exact superpose eq230797 eq213866
    | exact resolve eq213866 eq230797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213866
  have eq231073 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq230798
       have i₂ := eq213189
       grind)
    | exact superpose eq213189 eq230798
    | exact resolve eq230798 eq213189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213189 eq230798
  have eq231078 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq231073
       have i₂ := eq231009
       grind)
    | exact superpose eq231009 eq231073
    | exact resolve eq231073 eq231009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231009 eq231073
  have eq231079 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq231078
       have i₂ := eq230797
       grind)
    | exact superpose eq230797 eq231078
    | exact resolve eq231078 eq230797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230797 eq231078
  have eq231080 : False := by grind
  exact eq231080

/-- `Equation3385`: `x ◇ y = z ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation3385 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3385 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 (M.op X1 X3))
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X0 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X3 (M.op X2 X0) (M.op X1 X2)
       have i₂ := eq22 X1 X2 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X0) X1 X2
       have i₂ := eq22 X1 X2 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 X3) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X3 X0) (M.op X1 X3)
       have i₂ := eq22 X1 X3 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq22 X0 X0 X0
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq22 X0 X0 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq74 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X0 X1 X2 X3
       have i₂ := eq67 X1 (M.op X3 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq63 X0 X1 X2 X0
       have i₂ := eq67 X0 (M.op X2 X0) (M.op X0 X1)
       grind)
    | exact superpose eq67 eq63
    | exact resolve eq63 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq76 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq74 X0 X1 X2 X3
       have i₂ := eq67 X2 X3 X1
       grind)
    | (have i₁ := eq74 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq67 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq67 eq74
    | exact resolve eq74 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq83 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 X0) X1
       have i₂ := eq70 X0 (σ X1)
       grind)
    | exact superpose eq70 eq20
    | exact resolve eq20 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq92 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq47 X0 (σ X1) X2
       grind)
    | exact superpose eq47 eq20
    | (have j1 := eq47 (τ X0) X1 X2
       grind)
    | exact resolve eq20 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 (M.op X1 X2) X2 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X4 (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X2 X3))
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq131 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op (M.op X0 (M.op X3 X4)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X3 X4))
       have i₂ := eq21 X3 X4 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op (M.op X3 X4) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq131 X0 X1 X2 X3 X4
       have i₂ := eq67 (M.op X3 X4) (M.op X2 (M.op X0 X1)) X0
       grind)
    | (have i₁ := eq131 X0 X1 X0 X3 X4
       have i₂ := eq67 X0 (M.op X0 X1) (M.op X0 (M.op X3 X4))
       grind)
    | exact superpose eq67 eq131
    | exact resolve eq131 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq137 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X1 (M.op X4 (M.op X2 (M.op X3 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq130 X0 X1 X2 X3 X4
       have i₂ := eq67 X1 (M.op X4 (M.op X2 (M.op X3 X1))) X0
       grind)
    | (have i₁ := eq130 X0 X1 X2 X3 X0
       have i₂ := eq67 X0 (M.op X2 (M.op X3 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq67 eq130
    | exact resolve eq130 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq144 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq122 X0 X1 X2 X3
       have i₂ := eq67 (M.op (M.op X1 X2) X3) (M.op X0 X1) X0
       grind)
    | (have i₁ := eq122 X0 X1 X2 X3
       have i₂ := eq67 X0 X1 (M.op X0 (M.op (M.op X1 X2) X3))
       grind)
    | exact superpose eq67 eq122
    | exact resolve eq122 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq157 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op X3 (M.op X4 (M.op X2 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq136 X0 X1 X2 X3 X4
       have i₂ := eq67 X4 (M.op X2 (M.op X0 X1)) X3
       grind)
    | (have i₁ := eq136 X0 X1 X0 X3 X4
       have i₂ := eq67 X0 (M.op X0 X1) (M.op X3 X4)
       grind)
    | exact superpose eq67 eq136
    | exact resolve eq136 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq158 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq137 X0 x X2 X3 X4
       have i₂ := eq76 x X4 X3 X2
       grind)
    | exact superpose eq76 eq137
    | exact resolve eq137 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq137
  have eq165 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq144 X0 X1 X2 X3
       have i₂ := eq67 X3 (M.op X0 X1) (M.op X1 X2)
       grind)
    | (have i₁ := eq144 X0 X1 X2 X3
       have i₂ := eq67 X0 X1 (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq67 eq144
    | exact resolve eq144 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq176 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X3) X4)) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq158 X0 X2 X3 X4
       have i₂ := eq67 (M.op X2 X3) X4 X0
       grind)
    | (have i₁ := eq158 X0 X2 X3 (M.op X0 x)
       have i₂ := eq67 X0 x (M.op X0 (M.op X2 X3))
       grind)
    | exact superpose eq67 eq158
    | exact resolve eq158 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq181 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X3 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq165 X0 x X2 X3
       have i₂ := eq68 X0 x X3 X2
       grind)
    | exact superpose eq68 eq165
    | exact resolve eq165 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq165
  have eq188 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X3 X2))) = (M.op X0 (M.op X2 (M.op X3 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq176 X0 X4 X3 X2
       have i₂ := eq67 X3 X2 X4
       grind)
    | (have i₁ := eq176 X0 X2 X3 (M.op X0 x)
       have i₂ := eq67 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq67 eq176
    | exact resolve eq176 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq280 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X4 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X4 (M.op X0 X1) X3 X2
       have i₂ := eq67 X1 X2 X0
       grind)
    | exact superpose eq67 eq21
    | exact resolve eq21 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op (M.op X2 (M.op X3 X4)) (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X2 X3 (M.op X0 X1) X4
       have i₂ := eq67 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq67 eq21
    | exact resolve eq21 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq288 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X1)
       have i₂ := eq67 X1 (M.op X2 (M.op X3 (M.op X0 X1))) X0
       grind)
    | exact superpose eq67 eq8
    | exact resolve eq8 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X1 (M.op X2 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq288 x X1 X2 X3
       have i₂ := eq157 x X1 X3 X1 X2
       grind)
    | exact superpose eq157 eq288
    | exact resolve eq288 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq298 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op (M.op X3 X4) (M.op X0 (M.op X1 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq285 X0 X1 X2 X3 X4
       have i₂ := eq67 (M.op X3 X4) (M.op X0 (M.op X1 (M.op X2 X3))) X2
       grind)
    | (have i₁ := eq285 X0 X1 X2 X3 X4
       have i₂ := eq67 X0 (M.op X1 (M.op X2 X3)) (M.op X2 (M.op X3 X4))
       grind)
    | exact superpose eq67 eq285
    | exact resolve eq285 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq302 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X4 (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq280 X0 X1 X2 X3 X4
       have i₂ := eq67 (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 X1))) X4
       grind)
    | (have i₁ := eq280 X0 X1 X2 X0 X4
       have i₂ := eq67 X0 (M.op X4 (M.op X0 X1)) (M.op X4 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq67 eq280
    | exact resolve eq280 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq315 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 (M.op (M.op X3 X4) (M.op X0 X3))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq298 X0 X1 x X3 X4
       have i₂ := eq157 x X3 X1 (M.op X3 X4) X0
       grind)
    | exact superpose eq157 eq298
    | exact resolve eq298 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq317 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X4 (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq302 X0 X1 X2 X3 X4
       have i₂ := eq67 (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 X1))) X0
       grind)
    | (have i₁ := eq302 X0 X1 X2 X0 X4
       have i₂ := eq67 X0 (M.op X4 (M.op X0 X1)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq67 eq302
    | exact resolve eq302 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq324 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq315 X0 X1 X3 X4
       have i₂ := eq188 X1 X3 X0 (M.op X3 X4)
       grind)
    | (have i₁ := eq315 X0 X1 X3 X4
       have i₂ := eq188 X1 (M.op X3 X4) X0 X3
       grind)
    | exact superpose eq188 eq315
    | exact resolve eq315 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq325 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq317 X0 X1 X2 X3 x
       have i₂ := eq157 x (M.op X0 X1) X3 X0 (M.op X1 X2)
       grind)
    | exact superpose eq157 eq317
    | exact resolve eq317 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq317
  have eq331 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op X1 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq324 X0 X1 X3 X4
       have i₂ := eq67 X1 X4 X0
       grind)
    | (have i₁ := eq324 X0 X1 X3 (M.op X0 X1)
       have i₂ := eq67 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq67 eq324
    | exact resolve eq324 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq324
  have eq332 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq325 X0 X1 X2 X3
       have i₂ := eq188 X0 X1 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq325 X0 X1 X2 X3
       have i₂ := eq188 X0 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq188 eq325
    | exact resolve eq325 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq325
  have eq335 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op X3 (M.op X1 X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq332 x X1 X2 X3
       have i₂ := eq331 X1 X3 x (M.op X1 X2)
       grind)
    | (have i₁ := eq332 X1 X1 X2 x
       have i₂ := eq331 x X1 X3 (M.op X1 (M.op X1 (M.op X1 X2)))
       grind)
    | exact superpose eq331 eq332
    | exact resolve eq332 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq332
  have eq349 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq14
    | (have j1 := eq43 x x
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq790 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq181 x X1 X0
       grind)
    | exact superpose eq181 eq8
    | exact resolve eq8 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1633 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X1 X0 X0
       have i₂ := eq335 X0 X1 X1
       grind)
    | exact superpose eq335 eq295
    | exact resolve eq295 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq335
  have eq2262 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq1633 X1 X0
       grind)
    | (have i₁ := eq12 X1 X2
       have i₂ := eq1633 X0 X1
       grind)
    | exact superpose eq1633 eq12
    | (have j0 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8648 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq371 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq371
    | (have j0 := eq371 (τ X0)
       grind)
    | exact resolve eq371 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8656 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8648 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8648
    | (have j0 := eq8648 X0
       grind)
    | exact resolve eq8648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8648
  have eq8663 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8656 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8656
    | (have j0 := eq8656 X0
       grind)
    | exact resolve eq8656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8656
  have eq15168 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq349
       have i₂ := eq47 x X0 y
       grind)
    | exact superpose eq47 eq349
    | (have j1 := eq47 x X0 x
       grind)
    | exact resolve eq349 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq349
  have eq15170 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq15168 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15168
  have eq35130 : ∀ X0 X1 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ x) X1
       have i₂ := eq15170 X0
       grind)
    | exact superpose eq15170 eq83
    | (have j1 := eq15170 X1
       grind)
    | exact resolve eq83 eq15170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq15170
  have eq35231 : ∀ X0 X1 : G, x = (k x X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35130 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq35130
    | (have j0 := eq35130 X0 X0
       grind)
    | exact resolve eq35130 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35130
  have eq36544 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq35231 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35231
  have eq36545 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq36544 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36544
  have eq38191 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8663 x
       have i₂ := eq36545 x
       grind)
    | exact superpose eq36545 eq8663
    | (have j0 := eq8663 x
       grind)
    | (have r₁ := eq8663 x
       have r₂ := eq36545 x
       grind)
    | exact resolve eq8663 eq36545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38192 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq371 x
       have i₂ := eq36545 x
       grind)
    | exact superpose eq36545 eq371
    | (have j0 := eq371 x
       grind)
    | exact resolve eq371 eq36545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq38208 : ∀ X0 : G, (τ x) = (k (τ x) X0) := by
    intro X0
    first
    | (have i₁ := eq20 x X0
       have i₂ := eq36545 (σ X0)
       grind)
    | exact superpose eq36545 eq20
    | exact resolve eq20 eq36545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq36545
  have eq38210 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38192
  have eq38211 : x = (M.op x x) := by grind
  clear eq38191
  have eq39045 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq1633 X0 x
       have i₂ := eq38211
       grind)
    | exact superpose eq38211 eq1633
    | exact resolve eq1633 eq38211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633 eq38211
  have eq42724 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq8663 (τ x)
       have i₂ := eq38208 (τ x)
       grind)
    | exact superpose eq38208 eq8663
    | (have j0 := eq8663 (τ x)
       grind)
    | (have r₁ := eq8663 (τ x)
       have r₂ := eq38208 (τ x)
       grind)
    | exact resolve eq8663 eq38208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38208
  have eq42744 : (τ x) = (M.op (τ x) (τ x)) := by grind
  clear eq42724
  have eq42759 : x = (τ x) := by
    first
    | (have i₁ := eq42744
       have i₂ := eq39045 (τ x)
       grind)
    | exact superpose eq39045 eq42744
    | exact resolve eq42744 eq39045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42744
  have eq43369 : x = (σ x) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq42759
       grind)
    | exact superpose eq42759 eq10
    | exact resolve eq10 eq42759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43371 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0
       have i₂ := eq42759
       grind)
    | exact superpose eq42759 eq16
    | exact resolve eq16 eq42759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq43372 : ∀ X0 : G, (τ (k X0 x)) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq31 x X0
       have i₂ := eq42759
       grind)
    | exact superpose eq42759 eq31
    | exact resolve eq31 eq42759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq42759
  have eq44192 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43369
       grind)
    | exact superpose eq43369 eq14
    | exact resolve eq14 eq43369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107770 : ∀ X0 X1 : G, (k (τ X0) x) = (τ (M.op X0 x)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43372 X0
       have i₂ := eq2262 X1 X0 x
       grind)
    | exact superpose eq2262 eq43372
    | (have j1 := eq2262 X1 X0 x
       grind)
    | exact resolve eq43372 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262 eq43372
  have eq107855 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq107770 X0 x
       have i₂ := eq39045 x
       grind)
    | exact superpose eq39045 eq107770
    | (have j0 := eq107770 X0 x
       grind)
    | exact resolve eq107770 eq39045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107770
  have eq124275 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8663 (τ X0)
       have i₂ := eq92 X0 (τ X0) X1
       grind)
    | exact superpose eq92 eq8663
    | (have j0 := eq8663 (τ X0)
       have j1 := eq92 X0 X1 X1
       grind)
    | (have r₁ := eq8663 (τ X0)
       have r₂ := eq92 X0 (τ X0) x
       grind)
    | exact resolve eq8663 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq8663
  have eq124381 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq124275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124275
  have eq124445 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq124381 X0 X1
       have i₂ := eq39045 (τ X0)
       grind)
    | exact superpose eq39045 eq124381
    | (have j0 := eq124381 X0 X1
       grind)
    | exact resolve eq124381 eq39045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124381
  have eq131161 : ∀ X0 : G, (M.op (σ X0) x) = (σ (k X0 x)) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq43371 X0
       have i₂ := eq124445 (σ X0) x
       grind)
    | exact superpose eq124445 eq43371
    | (have j1 := eq124445 (σ X0) x
       grind)
    | exact resolve eq43371 eq124445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43371 eq124445
  have eq131195 : ∀ X0 : G, (M.op x (σ X0)) = (σ (k X0 x)) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq131161 X0
       have i₂ := eq790 (σ X0) x
       grind)
    | (have i₁ := eq131161 X0
       have i₂ := eq790 x (σ X0)
       grind)
    | exact superpose eq790 eq131161
    | (have j0 := eq131161 X0
       grind)
    | exact resolve eq131161 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131161
  have eq131261 : ∀ X0 : G, (M.op x (σ X0)) = (σ (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq131195 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq131195
    | (have j0 := eq131195 X0
       grind)
    | exact resolve eq131195 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131195
  have eq199328 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq107855 X0
       have i₂ := eq790 X0 x
       grind)
    | (have i₁ := eq107855 X0
       have i₂ := eq790 x X0
       grind)
    | exact superpose eq790 eq107855
    | (have j0 := eq107855 X0
       grind)
    | exact resolve eq107855 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq107855
  have eq222820 : ∀ X0 : G, (M.op x X0) = (σ (k (τ X0) x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x X0)
       have i₂ := eq199328 X0
       grind)
    | exact superpose eq199328 eq10
    | (have j1 := eq199328 X0
       grind)
    | exact resolve eq10 eq199328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199328
  have eq222842 : ∀ X0 : G, (M.op x X0) = (k X0 (σ x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq222820 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq222820
    | (have j0 := eq222820 X0
       grind)
    | exact resolve eq222820 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq222820
  have eq222881 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq222842 X0
       have i₂ := eq43369
       grind)
    | exact superpose eq43369 eq222842
    | (have j0 := eq222842 X0
       grind)
    | exact resolve eq222842 eq43369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43369 eq222842
  have eq223039 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq131261 X0
       have i₂ := eq222881 X0
       grind)
    | exact superpose eq222881 eq131261
    | (have j0 := eq131261 X0
       have j1 := eq222881 X0
       grind)
    | exact resolve eq131261 eq222881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131261 eq222881
  have eq223115 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq223039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223039
  have eq263692 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44192
       have i₂ := eq223115 y
       grind)
    | exact superpose eq223115 eq44192
    | (have j1 := eq223115 y
       grind)
    | (have r₁ := eq44192
       have r₂ := eq223115 y
       grind)
    | exact resolve eq44192 eq223115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44192 eq223115
  have eq263715 : x = y := by grind
  clear eq263692
  have eq265818 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq263715
       grind)
    | exact superpose eq263715 eq14
    | exact resolve eq14 eq263715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263715
  have eq265819 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq265818
       have i₂ := eq39045 x
       grind)
    | exact superpose eq39045 eq265818
    | exact resolve eq265818 eq39045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39045 eq265818
  have eq265821 : False := by grind
  exact eq265821

/-- `Equation3385`: `x ◇ y = z ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation3385 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3385 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 (M.op X1 X3))
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X0 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq16
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 (M.op X2 X0) (M.op X1 X2)
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X0) X1 X2
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 X3) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X3 X0) (M.op X1 X3)
       have i₂ := eq19 X1 X3 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43 X0 X1 X2 X3
       have i₂ := eq48 X1 (M.op X3 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq43 X0 X1 X2 X0
       have i₂ := eq48 X0 (M.op X2 X0) (M.op X0 X1)
       grind)
    | exact superpose eq48 eq43
    | exact resolve eq43 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 X3
       have i₂ := eq48 X2 X3 X1
       grind)
    | (have i₁ := eq55 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq48 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq48 eq55
    | exact resolve eq55 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq75 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 (M.op X1 X2) X2 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X1 X2 (M.op X2 X0) X3
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq18
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op X0 (M.op X0 X0)) X1) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq18 X0 X0 X0 X0
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    grind
  have eq113 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X4 (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X2 X3))
       have i₂ := eq18 X2 X3 X0 X1
       grind)
    | exact superpose eq18 eq19
    | exact resolve eq19 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op (M.op X0 (M.op X3 X4)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X3 X4))
       have i₂ := eq18 X3 X4 X0 X1
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op (M.op X3 X4) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq114 X0 X1 X2 X3 X4
       have i₂ := eq48 (M.op X3 X4) (M.op X2 (M.op X0 X1)) X0
       grind)
    | (have i₁ := eq114 X0 X1 X0 X3 X4
       have i₂ := eq48 X0 (M.op X0 X1) (M.op X0 (M.op X3 X4))
       grind)
    | exact superpose eq48 eq114
    | exact resolve eq114 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X1 (M.op X4 (M.op X2 (M.op X3 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq113 X0 X1 X2 X3 X4
       have i₂ := eq48 X1 (M.op X4 (M.op X2 (M.op X3 X1))) X0
       grind)
    | (have i₁ := eq113 X0 X1 X2 X3 X0
       have i₂ := eq48 X0 (M.op X2 (M.op X3 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq48 eq113
    | exact resolve eq113 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq118 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op X0 (M.op (M.op X0 X0) X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq48 (M.op X0 X0) X1 X0
       grind)
    | (have i₁ := eq110 X0 (M.op X0 X1)
       have i₂ := eq48 X0 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq48 eq110
    | (have j0 := eq110 X0 X1
       grind)
    | exact resolve eq110 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq122 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op X2 X3) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq106 X0 x X2 X3
       have i₂ := eq19 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq124 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq104 X0 X1 X2 X3
       have i₂ := eq48 (M.op (M.op X1 X2) X3) (M.op X0 X1) X0
       grind)
    | (have i₁ := eq104 X0 X1 X2 X3
       have i₂ := eq48 X0 X1 (M.op X0 (M.op (M.op X1 X2) X3))
       grind)
    | exact superpose eq48 eq104
    | exact resolve eq104 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq136 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op X3 (M.op X4 (M.op X2 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq115 X0 X1 X2 X3 X4
       have i₂ := eq48 X4 (M.op X2 (M.op X0 X1)) X3
       grind)
    | (have i₁ := eq115 X0 X1 X0 X3 X4
       have i₂ := eq48 X0 (M.op X0 X1) (M.op X3 X4)
       grind)
    | exact superpose eq48 eq115
    | exact resolve eq115 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq137 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq116 X0 x X2 X3 X4
       have i₂ := eq57 x X4 X3 X2
       grind)
    | exact superpose eq57 eq116
    | exact resolve eq116 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq116
  have eq139 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118 X0 X1
       have i₂ := eq48 X0 X1 X0
       grind)
    | (have i₁ := eq118 X0 (M.op X0 X1)
       have i₂ := eq48 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq48 eq118
    | (have j0 := eq118 X0 X1
       grind)
    | exact resolve eq118 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq143 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X2 X0) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq122 X0 X2 X3
       have i₂ := eq48 X3 X0 X2
       grind)
    | (have i₁ := eq122 (M.op X0 x) X2 X3
       have i₂ := eq48 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq48 eq122
    | exact resolve eq122 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq145 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq124 X0 X1 X2 X3
       have i₂ := eq48 X3 (M.op X0 X1) (M.op X1 X2)
       grind)
    | (have i₁ := eq124 X0 X1 X2 X3
       have i₂ := eq48 X0 X1 (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq48 eq124
    | exact resolve eq124 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq155 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X3) X4)) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq137 X0 X2 X3 X4
       have i₂ := eq48 (M.op X2 X3) X4 X0
       grind)
    | (have i₁ := eq137 X0 X2 X3 (M.op X0 x)
       have i₂ := eq48 X0 x (M.op X0 (M.op X2 X3))
       grind)
    | exact superpose eq48 eq137
    | exact resolve eq137 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq160 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X3 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq145 X0 x X2 X3
       have i₂ := eq51 X0 x X3 X2
       grind)
    | exact superpose eq51 eq145
    | exact resolve eq145 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq145
  have eq166 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X3 X2))) = (M.op X0 (M.op X2 (M.op X3 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq155 X0 X4 X3 X2
       have i₂ := eq48 X3 X2 X4
       grind)
    | (have i₁ := eq155 X0 X2 X3 (M.op X0 x)
       have i₂ := eq48 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq48 eq155
    | exact resolve eq155 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq288 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X4 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X4 (M.op X0 X1) X3 X2
       have i₂ := eq48 X1 X2 X0
       grind)
    | exact superpose eq48 eq18
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op (M.op X2 (M.op X3 X4)) (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X2 X3 (M.op X0 X1) X4
       have i₂ := eq48 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq48 eq18
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X1)
       have i₂ := eq48 X1 (M.op X2 (M.op X3 (M.op X0 X1))) X0
       grind)
    | exact superpose eq48 eq8
    | exact resolve eq8 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X1 (M.op X2 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq297 x X1 X2 X3
       have i₂ := eq136 x X1 X3 X1 X2
       grind)
    | exact superpose eq136 eq297
    | exact resolve eq297 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq301 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op (M.op X3 X4) (M.op X0 (M.op X1 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq294 X0 X1 X2 X3 X4
       have i₂ := eq48 (M.op X3 X4) (M.op X0 (M.op X1 (M.op X2 X3))) X2
       grind)
    | (have i₁ := eq294 X0 X1 X2 X3 X4
       have i₂ := eq48 X0 (M.op X1 (M.op X2 X3)) (M.op X2 (M.op X3 X4))
       grind)
    | exact superpose eq48 eq294
    | exact resolve eq294 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq306 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X4 (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq288 X0 X1 X2 X3 X4
       have i₂ := eq48 (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 X1))) X4
       grind)
    | (have i₁ := eq288 X0 X1 X2 X0 X4
       have i₂ := eq48 X0 (M.op X4 (M.op X0 X1)) (M.op X4 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq48 eq288
    | exact resolve eq288 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq320 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 (M.op (M.op X3 X4) (M.op X0 X3))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq301 X0 X1 x X3 X4
       have i₂ := eq136 x X3 X1 (M.op X3 X4) X0
       grind)
    | exact superpose eq136 eq301
    | exact resolve eq301 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq322 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X4 (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq306 X0 X1 X2 X3 X4
       have i₂ := eq48 (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 X1))) X0
       grind)
    | (have i₁ := eq306 X0 X1 X2 X0 X4
       have i₂ := eq48 X0 (M.op X4 (M.op X0 X1)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq48 eq306
    | exact resolve eq306 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq332 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq320 X0 X1 X3 X4
       have i₂ := eq166 X1 X3 X0 (M.op X3 X4)
       grind)
    | (have i₁ := eq320 X0 X1 X3 X4
       have i₂ := eq166 X1 (M.op X3 X4) X0 X3
       grind)
    | exact superpose eq166 eq320
    | exact resolve eq320 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq333 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq322 X0 X1 X2 X3 x
       have i₂ := eq136 x (M.op X0 X1) X3 X0 (M.op X1 X2)
       grind)
    | exact superpose eq136 eq322
    | exact resolve eq322 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq322
  have eq339 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op X1 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq332 X0 X1 X3 X4
       have i₂ := eq48 X1 X4 X0
       grind)
    | (have i₁ := eq332 X0 X1 X3 (M.op X0 X1)
       have i₂ := eq48 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq48 eq332
    | exact resolve eq332 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq340 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq333 X0 X1 X2 X3
       have i₂ := eq166 X0 X1 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq333 X0 X1 X2 X3
       have i₂ := eq166 X0 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq166 eq333
    | exact resolve eq333 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq343 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op X3 (M.op X1 X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq340 x X1 X2 X3
       have i₂ := eq339 X1 X3 x (M.op X1 X2)
       grind)
    | (have i₁ := eq340 X1 X1 X2 x
       have i₂ := eq339 x X1 X3 (M.op X1 (M.op X1 (M.op X1 X2)))
       grind)
    | exact superpose eq339 eq340
    | exact resolve eq340 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq340
  have eq368 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq782 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X1 X2 X0
       have i₂ := eq143 X1 X0 X2
       grind)
    | exact superpose eq143 eq48
    | exact resolve eq48 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq918 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160 X2 X1 (M.op X2 X0)
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq160
    | exact resolve eq160 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq919 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X1)) = (M.op X0 (M.op X2 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq160 (M.op X2 X3) X0 (M.op X2 (M.op X3 X1))
       have i₂ := eq18 X2 X3 X0 X1
       grind)
    | exact superpose eq18 eq160
    | exact resolve eq160 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq928 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq160 x X1 X0
       grind)
    | exact superpose eq160 eq8
    | exact resolve eq8 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X1))) = (M.op X0 (M.op X2 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq919 X0 X1 X2 X3
       have i₂ := eq48 X3 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq919 X0 X1 X2 X3
       have i₂ := eq48 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq48 eq919
    | exact resolve eq919 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq1087 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1 X0
       have i₂ := eq928 X1 X0
       grind)
    | (have i₁ := eq75 X1 X0
       have i₂ := eq928 X0 X1
       grind)
    | exact superpose eq928 eq75
    | (have j0 := eq75 X1 X0
       grind)
    | exact resolve eq75 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1192 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1)))) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (M.op X0 X1)
       have i₂ := eq48 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       grind)
    | exact superpose eq48 eq111
    | exact resolve eq111 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1219 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X0 (M.op X1 (M.op X0 (M.op X1 (M.op X0 X1))))) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1192 x X0
       have i₂ := eq918 X0 (M.op x X0) x
       grind)
    | (have i₁ := eq1192 X0 X1
       have i₂ := eq918 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq918 eq1192
    | exact resolve eq1192 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq1192
  have eq1232 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 (M.op X1 (M.op X0 X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1219 x X1
       have i₂ := eq298 X1 x (M.op X1 (M.op x X1))
       grind)
    | (have i₁ := eq1219 x X1
       have i₂ := eq298 X1 x x
       grind)
    | exact superpose eq298 eq1219
    | exact resolve eq1219 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1243 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1232 X0 X1
       have i₂ := eq8 X1 X0 X0
       grind)
    | exact superpose eq8 eq1232
    | exact resolve eq1232 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1561 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X1 X0 X0
       have i₂ := eq343 X0 X1 X1
       grind)
    | exact superpose eq343 eq298
    | exact resolve eq298 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1788 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq1804 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1087 X1 X1
       have i₂ := eq1561 X1 X0
       grind)
    | (have i₁ := eq1087 X1 X1
       have i₂ := eq1561 X0 X1
       grind)
    | exact superpose eq1561 eq1087
    | (have j0 := eq1087 X1 X1
       grind)
    | (have r₁ := eq1087 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq1561 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq1087 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq1561 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1087 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1806 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160 X2 X1 (M.op X1 X2)
       have i₂ := eq1561 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq160 X2 X1 (M.op X1 X2)
       have i₂ := eq1561 X0 (M.op X1 X2)
       grind)
    | exact superpose eq1561 eq160
    | exact resolve eq160 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq1818 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0
       have i₂ := eq1561 (τ X0) X1
       grind)
    | (have i₁ := eq21 X0
       have i₂ := eq1561 X0 (τ X0)
       grind)
    | exact superpose eq1561 eq21
    | exact resolve eq21 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1957 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 (M.op X0 X0)
       have i₂ := eq1788 X0 (σ X1)
       grind)
    | exact superpose eq1788 eq38
    | exact resolve eq38 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1788
  have eq4762 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op X2 (M.op X3 (M.op X3 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq166 X1 (M.op X3 X2) X3 X2
       have i₂ := eq1561 (M.op X3 X2) X0
       grind)
    | (have i₁ := eq166 X1 (M.op X3 X2) X3 X2
       have i₂ := eq1561 X0 (M.op X3 X2)
       grind)
    | exact superpose eq1561 eq166
    | exact resolve eq166 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq5056 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X3 X3)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq4762 X3 X1 x X0
       have i₂ := eq8 X0 X0 x
       grind)
    | exact superpose eq8 eq4762
    | exact resolve eq4762 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4762
  have eq8369 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq397 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq397
    | (have j0 := eq397 (τ X0)
       grind)
    | exact resolve eq397 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq8373 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8369 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8369
    | (have j0 := eq8369 X0
       grind)
    | exact resolve eq8369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8369
  have eq8377 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8373 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8373
    | (have j0 := eq8373 X0
       grind)
    | exact resolve eq8373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8373
  have eq13906 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq368
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq368
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq368 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq13907 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq13906
  have eq40176 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1957 (σ x) x
       have i₂ := eq13907
       grind)
    | exact superpose eq13907 eq1957
    | exact resolve eq1957 eq13907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13907
  have eq40256 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq40176 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq40176
    | exact resolve eq40176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40176
  have eq41761 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8377 y
       have i₂ := eq40256 y
       grind)
    | exact superpose eq40256 eq8377
    | (have j0 := eq8377 y
       grind)
    | (have r₁ := eq8377 y
       have r₂ := eq40256 y
       grind)
    | exact resolve eq8377 eq40256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40256
  have eq41782 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq41761
  have eq43114 : y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1243 y y
       have i₂ := eq41782
       grind)
    | exact superpose eq41782 eq1243
    | exact resolve eq1243 eq41782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243 eq41782
  have eq43130 : y = (k y y) := by
    first
    | (have j1 := eq1804 x y
       grind)
    | (have r₁ := eq43114
       have r₂ := eq1804 x y
       grind)
    | exact resolve eq43114 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804 eq43114
  have eq44464 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq43130
       grind)
    | exact superpose eq43130 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq43130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43130
  have eq44469 : y = (M.op y y) := by grind
  clear eq44464
  have eq46630 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq1561 X0 y
       have i₂ := eq44469
       grind)
    | exact superpose eq44469 eq1561
    | exact resolve eq1561 eq44469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq46634 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1806 y X0 X1
       have i₂ := eq44469
       grind)
    | exact superpose eq44469 eq1806
    | exact resolve eq1806 eq44469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806
  have eq46635 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1818 y x
       have i₂ := eq44469
       grind)
    | exact superpose eq44469 eq1818
    | exact resolve eq1818 eq44469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq46637 : ∀ X0 : G, (τ y) = (k X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq1957 y x
       have i₂ := eq44469
       grind)
    | exact superpose eq44469 eq1957
    | exact resolve eq1957 eq44469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq46639 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq5056 X1 X0 y
       have i₂ := eq44469
       grind)
    | exact superpose eq44469 eq5056
    | exact resolve eq5056 eq44469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5056 eq44469
  have eq51633 : (σ (σ y)) ≠ (σ (σ y)) ∨ (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) := by
    first
    | (have i₁ := eq397 (σ y)
       have i₂ := eq46635 (σ y)
       grind)
    | exact superpose eq46635 eq397
    | (have j0 := eq397 (σ y)
       grind)
    | exact resolve eq397 eq46635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq46635
  have eq51660 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) := by grind
  clear eq51633
  have eq51675 : y = (σ (σ y)) := by
    first
    | (have i₁ := eq51660
       have i₂ := eq46630 (σ (σ y))
       grind)
    | exact superpose eq46630 eq51660
    | exact resolve eq51660 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51660
  have eq54444 : (σ y) = (τ y) := by
    first
    | (have i₁ := eq9 (σ y)
       have i₂ := eq51675
       grind)
    | exact superpose eq51675 eq9
    | exact resolve eq9 eq51675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51675
  have eq55303 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq8377 (τ y)
       have i₂ := eq46637 (τ y)
       grind)
    | exact superpose eq46637 eq8377
    | (have j0 := eq8377 (τ y)
       grind)
    | (have r₁ := eq8377 (τ y)
       have r₂ := eq46637 (τ y)
       grind)
    | exact resolve eq8377 eq46637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8377 eq46637
  have eq55331 : (τ y) = (M.op (τ y) (τ y)) := by grind
  clear eq55303
  have eq55355 : y = (τ y) := by
    first
    | (have i₁ := eq55331
       have i₂ := eq46630 (τ y)
       grind)
    | exact superpose eq46630 eq55331
    | exact resolve eq55331 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55331
  have eq56638 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq55355
       grind)
    | exact superpose eq55355 eq10
    | exact resolve eq10 eq55355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55355
  have eq57604 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56638
       grind)
    | exact superpose eq56638 eq14
    | exact resolve eq14 eq56638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57629 : ∀ X0 : G, (τ (M.op y y)) = X0 ∨ (M.op y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq379 y x
       have i₂ := eq56638
       grind)
    | exact superpose eq56638 eq379
    | exact resolve eq379 eq56638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq57630 : ∀ X0 : G, (τ y) = X0 ∨ (M.op y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq57629 X0
       have i₂ := eq46630 y
       grind)
    | exact superpose eq46630 eq57629
    | (have j0 := eq57629 X0
       grind)
    | exact resolve eq57629 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57629
  have eq57643 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq57604
       have i₂ := eq928 (σ x) y
       grind)
    | (have i₁ := eq57604
       have i₂ := eq928 y (σ x)
       grind)
    | exact superpose eq928 eq57604
    | exact resolve eq57604 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57604
  have eq57644 : ∀ X0 : G, (σ y) = X0 ∨ (M.op y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq57630 X0
       have i₂ := eq54444
       grind)
    | exact superpose eq54444 eq57630
    | (have j0 := eq57630 X0
       grind)
    | exact resolve eq57630 eq54444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54444 eq57630
  have eq57656 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq57644 X0
       have i₂ := eq56638
       grind)
    | exact superpose eq56638 eq57644
    | (have j0 := eq57644 X0
       grind)
    | exact resolve eq57644 eq56638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57644
  have eq69150 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op (M.op X0 X0) (M.op (M.op X0 X0) y)) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq139 (M.op X1 X1) X1
       have i₂ := eq46639 (M.op X1 X1) X1
       grind)
    | exact superpose eq46639 eq139
    | exact resolve eq139 eq46639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq69406 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op (M.op X0 X0) (M.op y (M.op X0 X0))) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69150 X0 X1
       have i₂ := eq782 (M.op X0 X0) (M.op X0 X0) y
       grind)
    | (have i₁ := eq69150 X0 X1
       have i₂ := eq782 (M.op X0 X0) y (M.op X0 X0)
       grind)
    | exact superpose eq782 eq69150
    | (have j0 := eq69150 X0 X1
       grind)
    | exact resolve eq69150 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq69150
  have eq69675 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op X0 (M.op (M.op X0 X0) (M.op y X0))) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69406 X0 X1
       have i₂ := eq967 X0 X0 (M.op X0 X0) y
       grind)
    | (have i₁ := eq69406 X1 X1
       have i₂ := eq967 (M.op X1 X1) X1 y X1
       grind)
    | exact superpose eq967 eq69406
    | (have j0 := eq69406 X0 X1
       grind)
    | exact resolve eq69406 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq69406
  have eq69808 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op (M.op X0 X0) y) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69675 X0 X1
       have i₂ := eq8 (M.op X0 X0) y X0
       grind)
    | exact superpose eq8 eq69675
    | (have j0 := eq69675 X0 X1
       grind)
    | exact resolve eq69675 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69675
  have eq69850 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op y (M.op X0 X0)) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69808 X0 X1
       have i₂ := eq928 (M.op X0 X0) y
       grind)
    | (have i₁ := eq69808 X0 X1
       have i₂ := eq928 y (M.op X0 X0)
       grind)
    | exact superpose eq928 eq69808
    | (have j0 := eq69808 X0 X1
       grind)
    | exact resolve eq69808 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69808
  have eq69867 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k (M.op y y) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69850 X0 X1
       have i₂ := eq46639 y X0
       grind)
    | exact superpose eq46639 eq69850
    | (have j0 := eq69850 X0 X1
       grind)
    | exact resolve eq69850 eq46639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69850
  have eq69878 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) = (k y X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69867 X0 X1
       have i₂ := eq46630 y
       grind)
    | exact superpose eq46630 eq69867
    | (have j0 := eq69867 X0 X1
       grind)
    | exact resolve eq69867 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69867
  have eq69883 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k y X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69878 X0 X1
       have i₂ := eq343 (M.op X0 X0) X1 (M.op X0 X0)
       grind)
    | exact superpose eq343 eq69878
    | (have j0 := eq69878 X0 X1
       grind)
    | exact resolve eq69878 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq69878
  have eq69884 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k y X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69883 X0 X1
       have i₂ := eq48 X0 X1 X0
       grind)
    | (have i₁ := eq69883 X0 (M.op X0 X1)
       have i₂ := eq48 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq48 eq69883
    | (have j0 := eq69883 X0 X1
       grind)
    | exact resolve eq69883 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq69883
  have eq69885 : ∀ X0 X1 : G, (M.op X1 y) = (k y X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69884 X0 X1
       have i₂ := eq46634 X0 X1
       grind)
    | exact superpose eq46634 eq69884
    | (have j0 := eq69884 X0 X1
       grind)
    | exact resolve eq69884 eq46634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46634 eq69884
  have eq69886 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = X1 ∨ (M.op X1 y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69885 X0 X1
       have i₂ := eq928 (M.op X0 X0) y
       grind)
    | (have i₁ := eq69885 X0 X1
       have i₂ := eq928 y (M.op X0 X0)
       grind)
    | exact superpose eq928 eq69885
    | (have j0 := eq69885 X0 X1
       grind)
    | exact resolve eq69885 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq69885
  have eq69887 : ∀ X1 : G, (M.op y y) = X1 ∨ (M.op X1 y) = (k y X1) := by
    intro X1
    first
    | (have i₁ := eq69886 x X1
       have i₂ := eq46639 y x
       grind)
    | exact superpose eq46639 eq69886
    | (have j0 := eq69886 x X1
       grind)
    | exact resolve eq69886 eq46639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46639 eq69886
  have eq69888 : ∀ X1 : G, (M.op X1 y) = (k y X1) ∨ y = X1 := by
    intro X1
    first
    | (have i₁ := eq69887 X1
       have i₂ := eq46630 y
       grind)
    | exact superpose eq46630 eq69887
    | (have j0 := eq69887 X1
       grind)
    | exact resolve eq69887 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69887
  have eq204728 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq57656 X0
       have i₂ := eq69888 X0
       grind)
    | exact superpose eq69888 eq57656
    | (have j0 := eq57656 X0
       have j1 := eq69888 X0
       grind)
    | exact resolve eq57656 eq69888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57656 eq69888
  have eq204804 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq204728 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204728
  have eq218226 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq57643
       have i₂ := eq204804 x
       grind)
    | exact superpose eq204804 eq57643
    | (have j1 := eq204804 x
       grind)
    | (have r₁ := eq57643
       have r₂ := eq204804 x
       grind)
    | exact resolve eq57643 eq204804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57643 eq204804
  have eq218245 : x = y := by grind
  clear eq218226
  have eq218371 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq218245
       grind)
    | exact superpose eq218245 eq14
    | exact resolve eq14 eq218245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218245
  have eq218549 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq218371
       have i₂ := eq46630 x
       grind)
    | exact superpose eq46630 eq218371
    | exact resolve eq218371 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218371
  have eq218571 : y ≠ (σ y) := by
    first
    | (have i₁ := eq218549
       have i₂ := eq46630 (σ x)
       grind)
    | exact superpose eq46630 eq218549
    | exact resolve eq218549 eq46630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46630 eq218549
  have eq218585 : False := by grind
  exact eq218585

/-- `Equation3385`: `x ◇ y = z ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3385 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3385 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 (M.op X1 X3))
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X0 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 (M.op X2 X0) (M.op X1 X2)
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X0) X1 X2
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 X3) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X3 X0) (M.op X1 X3)
       have i₂ := eq19 X1 X3 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44 X0 X1 X2 X3
       have i₂ := eq49 X1 (M.op X3 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq44 X0 X1 X2 X0
       have i₂ := eq49 X0 (M.op X2 X0) (M.op X0 X1)
       grind)
    | exact superpose eq49 eq44
    | exact resolve eq44 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X0 X1 X2 X3
       have i₂ := eq49 X2 X3 X1
       grind)
    | (have i₁ := eq56 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq49 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq49 eq56
    | exact resolve eq56 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 (M.op X1 X2) X2 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X4 (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X2 X3))
       have i₂ := eq18 X2 X3 X0 X1
       grind)
    | exact superpose eq18 eq19
    | exact resolve eq19 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq116 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op (M.op X0 (M.op X3 X4)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X3 X4))
       have i₂ := eq18 X3 X4 X0 X1
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op (M.op X3 X4) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq116 X0 X1 X2 X3 X4
       have i₂ := eq49 (M.op X3 X4) (M.op X2 (M.op X0 X1)) X0
       grind)
    | (have i₁ := eq116 X0 X1 X0 X3 X4
       have i₂ := eq49 X0 (M.op X0 X1) (M.op X0 (M.op X3 X4))
       grind)
    | exact superpose eq49 eq116
    | exact resolve eq116 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X1 (M.op X4 (M.op X2 (M.op X3 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq115 X0 X1 X2 X3 X4
       have i₂ := eq49 X1 (M.op X4 (M.op X2 (M.op X3 X1))) X0
       grind)
    | (have i₁ := eq115 X0 X1 X2 X3 X0
       have i₂ := eq49 X0 (M.op X2 (M.op X3 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq49 eq115
    | exact resolve eq115 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq126 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq106 X0 X1 X2 X3
       have i₂ := eq49 (M.op (M.op X1 X2) X3) (M.op X0 X1) X0
       grind)
    | (have i₁ := eq106 X0 X1 X2 X3
       have i₂ := eq49 X0 X1 (M.op X0 (M.op (M.op X1 X2) X3))
       grind)
    | exact superpose eq49 eq106
    | exact resolve eq106 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq138 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op X3 (M.op X4 (M.op X2 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq117 X0 X1 X2 X3 X4
       have i₂ := eq49 X4 (M.op X2 (M.op X0 X1)) X3
       grind)
    | (have i₁ := eq117 X0 X1 X0 X3 X4
       have i₂ := eq49 X0 (M.op X0 X1) (M.op X3 X4)
       grind)
    | exact superpose eq49 eq117
    | exact resolve eq117 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq139 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq118 X0 x X2 X3 X4
       have i₂ := eq58 x X4 X3 X2
       grind)
    | exact superpose eq58 eq118
    | exact resolve eq118 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq118
  have eq147 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq126 X0 X1 X2 X3
       have i₂ := eq49 X3 (M.op X0 X1) (M.op X1 X2)
       grind)
    | (have i₁ := eq126 X0 X1 X2 X3
       have i₂ := eq49 X0 X1 (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq49 eq126
    | exact resolve eq126 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq157 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X3) X4)) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq139 X0 X2 X3 X4
       have i₂ := eq49 (M.op X2 X3) X4 X0
       grind)
    | (have i₁ := eq139 X0 X2 X3 (M.op X0 x)
       have i₂ := eq49 X0 x (M.op X0 (M.op X2 X3))
       grind)
    | exact superpose eq49 eq139
    | exact resolve eq139 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq162 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X3 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq147 X0 x X2 X3
       have i₂ := eq52 X0 x X3 X2
       grind)
    | exact superpose eq52 eq147
    | exact resolve eq147 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq147
  have eq168 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X3 X2))) = (M.op X0 (M.op X2 (M.op X3 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq157 X0 X4 X3 X2
       have i₂ := eq49 X3 X2 X4
       grind)
    | (have i₁ := eq157 X0 X2 X3 (M.op X0 x)
       have i₂ := eq49 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq49 eq157
    | exact resolve eq157 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq185 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq199 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq185
    | exact resolve eq185 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq320 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq330 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq361 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq322 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq322
    | (have j0 := eq322 X0
       grind)
    | exact resolve eq322 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq703 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X4 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X4 (M.op X0 X1) X3 X2
       have i₂ := eq49 X1 X2 X0
       grind)
    | exact superpose eq49 eq18
    | exact resolve eq18 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op (M.op X2 (M.op X3 X4)) (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X2 X3 (M.op X0 X1) X4
       have i₂ := eq49 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq49 eq18
    | exact resolve eq18 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq715 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X1)
       have i₂ := eq49 X1 (M.op X2 (M.op X3 (M.op X0 X1))) X0
       grind)
    | exact superpose eq49 eq8
    | exact resolve eq8 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X1 (M.op X2 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq715 x X1 X2 X3
       have i₂ := eq138 x X1 X3 X1 X2
       grind)
    | exact superpose eq138 eq715
    | exact resolve eq715 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq719 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op (M.op X3 X4) (M.op X0 (M.op X1 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq712 X0 X1 X2 X3 X4
       have i₂ := eq49 (M.op X3 X4) (M.op X0 (M.op X1 (M.op X2 X3))) X2
       grind)
    | (have i₁ := eq712 X0 X1 X2 X3 X4
       have i₂ := eq49 X0 (M.op X1 (M.op X2 X3)) (M.op X2 (M.op X3 X4))
       grind)
    | exact superpose eq49 eq712
    | exact resolve eq712 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq727 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X4 (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq703 X0 X1 X2 X3 X4
       have i₂ := eq49 (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 X1))) X4
       grind)
    | (have i₁ := eq703 X0 X1 X2 X0 X4
       have i₂ := eq49 X0 (M.op X4 (M.op X0 X1)) (M.op X4 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq49 eq703
    | exact resolve eq703 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq746 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 (M.op (M.op X3 X4) (M.op X0 X3))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq719 X0 X1 x X3 X4
       have i₂ := eq138 x X3 X1 (M.op X3 X4) X0
       grind)
    | exact superpose eq138 eq719
    | exact resolve eq719 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq751 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X4 (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq727 X0 X1 X2 X3 X4
       have i₂ := eq49 (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 X1))) X0
       grind)
    | (have i₁ := eq727 X0 X1 X2 X0 X4
       have i₂ := eq49 X0 (M.op X4 (M.op X0 X1)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq49 eq727
    | exact resolve eq727 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq764 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq746 X0 X1 X3 X4
       have i₂ := eq168 X1 X3 X0 (M.op X3 X4)
       grind)
    | (have i₁ := eq746 X0 X1 X3 X4
       have i₂ := eq168 X1 (M.op X3 X4) X0 X3
       grind)
    | exact superpose eq168 eq746
    | exact resolve eq746 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq768 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq751 X0 X1 X2 X3 x
       have i₂ := eq138 x (M.op X0 X1) X3 X0 (M.op X1 X2)
       grind)
    | exact superpose eq138 eq751
    | exact resolve eq751 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq751
  have eq777 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op X1 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq764 X0 X1 X3 X4
       have i₂ := eq49 X1 X4 X0
       grind)
    | (have i₁ := eq764 X0 X1 X3 (M.op X0 X1)
       have i₂ := eq49 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq49 eq764
    | exact resolve eq764 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq781 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq768 X0 X1 X2 X3
       have i₂ := eq168 X0 X1 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq768 X0 X1 X2 X3
       have i₂ := eq168 X0 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq168 eq768
    | exact resolve eq768 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq788 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op X3 (M.op X1 X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq781 x X1 X2 X3
       have i₂ := eq777 X1 X3 x (M.op X1 X2)
       grind)
    | (have i₁ := eq781 X1 X1 X2 x
       have i₂ := eq777 x X1 X3 (M.op X1 (M.op X1 (M.op X1 X2)))
       grind)
    | exact superpose eq777 eq781
    | exact resolve eq781 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq781
  have eq985 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq162 x X1 X0
       grind)
    | exact superpose eq162 eq8
    | exact resolve eq8 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1144 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1 X0
       have i₂ := eq985 X1 X0
       grind)
    | (have i₁ := eq76 X1 X0
       have i₂ := eq985 X0 X1
       grind)
    | exact superpose eq985 eq76
    | (have j0 := eq76 X1 X0
       grind)
    | exact resolve eq76 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1607 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X1 X0 X0
       have i₂ := eq788 X0 X1 X1
       grind)
    | exact superpose eq788 eq716
    | exact resolve eq716 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq788
  have eq1862 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1144 X1 X1
       have i₂ := eq1607 X1 X0
       grind)
    | (have i₁ := eq1144 X1 X1
       have i₂ := eq1607 X0 X1
       grind)
    | exact superpose eq1607 eq1144
    | (have j0 := eq1144 X1 X1
       grind)
    | (have r₁ := eq1144 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq1607 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq1144 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq1607 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1144 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1864 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162 X2 X1 (M.op X1 X2)
       have i₂ := eq1607 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq162 X2 X1 (M.op X1 X2)
       have i₂ := eq1607 X0 (M.op X1 X2)
       grind)
    | exact superpose eq1607 eq162
    | exact resolve eq162 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq1875 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199 X1
       have i₂ := eq1607 (σ X1) X0
       grind)
    | (have i₁ := eq199 X1
       have i₂ := eq1607 X0 (σ X1)
       grind)
    | exact superpose eq1607 eq199
    | exact resolve eq199 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq3844 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op X2 (M.op X3 (M.op X3 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq168 X1 (M.op X3 X2) X3 X2
       have i₂ := eq1607 (M.op X3 X2) X0
       grind)
    | (have i₁ := eq168 X1 (M.op X3 X2) X3 X2
       have i₂ := eq1607 X0 (M.op X3 X2)
       grind)
    | exact superpose eq1607 eq168
    | exact resolve eq168 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq4104 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X3 X3)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3844 X3 X1 x X0
       have i₂ := eq8 X0 X0 x
       grind)
    | exact superpose eq8 eq3844
    | exact resolve eq3844 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3844
  have eq5923 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq348 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq348
    | (have j0 := eq348 (τ X0)
       grind)
    | exact resolve eq348 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq5932 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5923 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5923
    | (have j0 := eq5923 X0
       grind)
    | exact resolve eq5923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5923
  have eq5939 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5932 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5932
    | (have j0 := eq5932 X0
       grind)
    | exact resolve eq5932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5932
  have eq11529 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq320
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq320
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq320 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq11530 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq11529
  have eq12320 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (k (τ X0) (τ X0))
       have i₂ := eq361 (τ X0)
       grind)
    | exact superpose eq361 eq16
    | (have j1 := eq361 (τ X0)
       grind)
    | exact resolve eq16 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq361
  have eq12354 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12320 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq12320
    | (have j0 := eq12320 X0
       grind)
    | exact resolve eq12320 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq12320
  have eq12369 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12354 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12354
    | (have j0 := eq12354 X0
       grind)
    | exact resolve eq12354 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12354
  have eq12376 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12369 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12369
    | (have j0 := eq12369 X0
       grind)
    | exact resolve eq12369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12369
  have eq52330 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1875 (σ x) X0
       have i₂ := eq11530
       grind)
    | exact superpose eq11530 eq1875
    | exact resolve eq1875 eq11530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11530
  have eq52436 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52330 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq52330
    | exact resolve eq52330 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52330
  have eq52891 : y = (k y y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12376 y
       have i₂ := eq52436 y
       grind)
    | exact superpose eq52436 eq12376
    | (have j0 := eq12376 y
       have j1 := eq52436 y
       grind)
    | exact resolve eq12376 eq52436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12376 eq52436
  have eq52927 : y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq76 y y
       grind)
    | (have r₁ := eq52891
       have r₂ := eq76 y y
       grind)
    | exact resolve eq52891 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq52891
  have eq52934 : y = (k y y) := by
    first
    | (have j1 := eq1862 x y
       grind)
    | (have r₁ := eq52927
       have r₂ := eq1862 x y
       grind)
    | exact resolve eq52927 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862 eq52927
  have eq53729 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq52934
       grind)
    | exact superpose eq52934 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq52934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52934
  have eq53737 : y = (M.op y y) := by grind
  clear eq53729
  have eq54376 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq1607 X0 y
       have i₂ := eq53737
       grind)
    | exact superpose eq53737 eq1607
    | exact resolve eq1607 eq53737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq54380 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1864 y X0 X1
       have i₂ := eq53737
       grind)
    | exact superpose eq53737 eq1864
    | exact resolve eq1864 eq53737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq54381 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1875 y X0
       have i₂ := eq53737
       grind)
    | exact superpose eq53737 eq1875
    | exact resolve eq1875 eq53737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq54388 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq4104 X1 X0 y
       have i₂ := eq53737
       grind)
    | exact superpose eq53737 eq4104
    | exact resolve eq4104 eq53737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104 eq53737
  have eq56782 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq5939 (τ y)
       have i₂ := eq54381 (τ y)
       grind)
    | exact superpose eq54381 eq5939
    | (have j0 := eq5939 (τ y)
       grind)
    | (have r₁ := eq5939 (τ y)
       have r₂ := eq54381 (τ y)
       grind)
    | exact resolve eq5939 eq54381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5939 eq54381
  have eq56811 : (τ y) = (M.op (τ y) (τ y)) := by grind
  clear eq56782
  have eq56829 : y = (τ y) := by
    first
    | (have i₁ := eq56811
       have i₂ := eq54376 (τ y)
       grind)
    | exact superpose eq54376 eq56811
    | exact resolve eq56811 eq54376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56811
  have eq57672 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq56829
       grind)
    | exact superpose eq56829 eq10
    | exact resolve eq10 eq56829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59082 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57672
       grind)
    | exact superpose eq57672 eq14
    | exact resolve eq14 eq57672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59113 : ∀ X0 : G, (τ (M.op y y)) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq330 y x
       have i₂ := eq57672
       grind)
    | exact superpose eq57672 eq330
    | exact resolve eq330 eq57672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq59126 : ∀ X0 : G, (τ y) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq59113 X0
       have i₂ := eq54376 y
       grind)
    | exact superpose eq54376 eq59113
    | (have j0 := eq59113 X0
       grind)
    | exact resolve eq59113 eq54376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59113
  have eq59139 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq59082
       have i₂ := eq985 (σ x) y
       grind)
    | (have i₁ := eq59082
       have i₂ := eq985 y (σ x)
       grind)
    | exact superpose eq985 eq59082
    | exact resolve eq59082 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59082
  have eq59144 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq59126 X0
       have i₂ := eq56829
       grind)
    | exact superpose eq56829 eq59126
    | (have j0 := eq59126 X0
       grind)
    | exact resolve eq59126 eq56829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56829 eq59126
  have eq87719 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) y) X1) = (k (M.op (M.op X0 X0) y) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X1) X1
       have i₂ := eq54388 (M.op X1 X1) X1
       grind)
    | exact superpose eq54388 eq50
    | exact resolve eq50 eq54388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq87996 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X0)) X1) = (k (M.op y (M.op X0 X0)) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87719 X0 X1
       have i₂ := eq985 (M.op X0 X0) y
       grind)
    | (have i₁ := eq87719 X0 X1
       have i₂ := eq985 y (M.op X0 X0)
       grind)
    | exact superpose eq985 eq87719
    | (have j0 := eq87719 X0 X1
       grind)
    | exact resolve eq87719 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87719
  have eq88292 : ∀ X0 X1 : G, (k (M.op y y) X1) = (M.op (M.op y y) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87996 X1 X1
       have i₂ := eq54388 y X1
       grind)
    | exact superpose eq54388 eq87996
    | (have j0 := eq87996 X0 X1
       grind)
    | exact resolve eq87996 eq54388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87996
  have eq88441 : ∀ X0 X1 : G, (M.op y (M.op y X1)) = (k (M.op y y) X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88292 X0 X1
       have i₂ := eq49 y X1 y
       grind)
    | (have i₁ := eq88292 X0 (M.op X0 X1)
       have i₂ := eq49 X0 X1 (M.op y y)
       grind)
    | exact superpose eq49 eq88292
    | (have j0 := eq88292 X0 X1
       grind)
    | exact resolve eq88292 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq88292
  have eq88493 : ∀ X0 X1 : G, (k y X1) = (M.op y (M.op y X1)) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88441 X0 X1
       have i₂ := eq54376 y
       grind)
    | exact superpose eq54376 eq88441
    | (have j0 := eq88441 X0 X1
       grind)
    | exact resolve eq88441 eq54376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88441
  have eq88512 : ∀ X0 X1 : G, (M.op X1 y) = (k y X1) ∨ (M.op (M.op X0 X0) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88493 X0 X1
       have i₂ := eq54380 y X1
       grind)
    | exact superpose eq54380 eq88493
    | (have j0 := eq88493 X0 X1
       grind)
    | exact resolve eq88493 eq54380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54380 eq88493
  have eq88521 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = X1 ∨ (M.op X1 y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq88512 X0 X1
       have i₂ := eq985 (M.op X0 X0) y
       grind)
    | (have i₁ := eq88512 X0 X1
       have i₂ := eq985 y (M.op X0 X0)
       grind)
    | exact superpose eq985 eq88512
    | (have j0 := eq88512 X0 X1
       grind)
    | exact resolve eq88512 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985 eq88512
  have eq88526 : ∀ X1 : G, (M.op y y) = X1 ∨ (M.op X1 y) = (k y X1) := by
    intro X1
    first
    | (have i₁ := eq88521 x X1
       have i₂ := eq54388 y x
       grind)
    | exact superpose eq54388 eq88521
    | (have j0 := eq88521 x X1
       grind)
    | exact resolve eq88521 eq54388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54388 eq88521
  have eq88528 : ∀ X1 : G, (M.op X1 y) = (k y X1) ∨ y = X1 := by
    intro X1
    first
    | (have i₁ := eq88526 X1
       have i₂ := eq54376 y
       grind)
    | exact superpose eq54376 eq88526
    | (have j0 := eq88526 X1
       grind)
    | exact resolve eq88526 eq54376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88526
  have eq263589 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq59144 X0
       have i₂ := eq88528 X0
       grind)
    | exact superpose eq88528 eq59144
    | (have j0 := eq59144 X0
       have j1 := eq88528 X0
       grind)
    | exact resolve eq59144 eq88528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59144 eq88528
  have eq263674 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq263589 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263589
  have eq267427 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq59139
       have i₂ := eq263674 x
       grind)
    | exact superpose eq263674 eq59139
    | (have j1 := eq263674 x
       grind)
    | (have r₁ := eq59139
       have r₂ := eq263674 x
       grind)
    | exact resolve eq59139 eq263674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59139 eq263674
  have eq267437 : x = y := by grind
  clear eq267427
  have eq267812 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq267437
       grind)
    | exact superpose eq267437 eq14
    | exact resolve eq14 eq267437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267437
  have eq267935 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq267812
       have i₂ := eq54376 x
       grind)
    | exact superpose eq54376 eq267812
    | exact resolve eq267812 eq54376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267812
  have eq267960 : y ≠ (σ y) := by
    first
    | (have i₁ := eq267935
       have i₂ := eq54376 (σ x)
       grind)
    | exact superpose eq54376 eq267935
    | exact resolve eq267935 eq54376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54376 eq267935
  have eq267976 : False := by grind
  exact eq267976

/-- `Equation3398`: `x ◇ y = z ◇ (y ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3398 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3398 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3398.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X1 (M.op X0 X2)) (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X1 (M.op X0 X2))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq19 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X2 X1) X0
       have i₂ := eq19 X2 X0 X1
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 (M.op X1 X2)
       have i₂ := eq19 X1 (M.op X0 (M.op X1 X2)) X2
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq55 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq69 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq28 X1 (τ X0)
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X1 (τ X0)
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq102 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X0 (M.op X3 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X3 X0 X2 (M.op X3 X1)
       have i₂ := eq19 X3 X0 X1
       grind)
    | exact superpose eq19 eq18
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq114 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X1 (M.op X3 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq102 x X1 X2 X3
       have i₂ := eq19 x X1 (M.op X3 X2)
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq102
  have eq128 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq142 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq128 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq128
    | exact resolve eq128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq244 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq254 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq13
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq281 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq246 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq246
    | (have j0 := eq246 X0
       grind)
    | exact resolve eq246 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq471 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X2 X1
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq8 X2 X2 X1
       have i₂ := eq50 X2 X1 X0
       grind)
    | exact superpose eq50 eq8
    | exact resolve eq8 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq471 X2 x X0
       have i₂ := eq8 X2 X2 x
       grind)
    | exact superpose eq8 eq471
    | exact resolve eq471 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq555 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 X3 X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq51 X0 X1 X2
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq560 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X0 (M.op X1 (M.op X2 X3))) X3
       have i₂ := eq51 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq51 eq8
    | exact resolve eq8 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq555 X0 X1 X2 X3
       have i₂ := eq114 X1 (M.op X0 (M.op X1 X2)) X0
       grind)
    | (have i₁ := eq555 X0 X1 X2 X3
       have i₂ := eq114 (M.op X0 (M.op X1 X2)) X1 X0
       grind)
    | exact superpose eq114 eq555
    | exact resolve eq555 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq555
  have eq585 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq562 X0 x X2 X3
       have i₂ := eq560 X0 X0 x X2
       grind)
    | exact superpose eq560 eq562
    | exact resolve eq562 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq562
  have eq646 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq488 X1 X0
       grind)
    | (have i₁ := eq12 X1 X2
       have i₂ := eq488 X0 X1
       grind)
    | exact superpose eq488 eq12
    | (have j0 := eq12 X0 X2
       grind)
    | exact resolve eq12 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 X1
       have i₂ := eq488 X1 X0
       grind)
    | (have i₁ := eq70 X1 X1
       have i₂ := eq488 X0 X1
       grind)
    | exact superpose eq488 eq70
    | (have j0 := eq70 X1 X1
       grind)
    | (have r₁ := eq70 (M.op x x) (M.op x x)
       have r₂ := eq488 (M.op x x) x
       grind)
    | (have r₁ := eq70 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq488 X0 (M.op X0 X0)
       grind)
    | exact resolve eq70 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 X1
       have i₂ := eq488 (σ X1) X0
       grind)
    | (have i₁ := eq142 X1
       have i₂ := eq488 X0 (σ X1)
       grind)
    | exact superpose eq488 eq142
    | exact resolve eq142 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq7148 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq272 (M.op X0 X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq272
    | (have j0 := eq272 (M.op X0 X0)
       grind)
    | exact resolve eq272 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq7153 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq272 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq272
    | (have j0 := eq272 (τ X0)
       grind)
    | exact resolve eq272 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq7155 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq7148 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7148
  have eq7163 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7153 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7153
    | (have j0 := eq7153 X0
       grind)
    | exact resolve eq7153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7153
  have eq7170 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7163 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7163
    | (have j0 := eq7163 X0
       grind)
    | exact resolve eq7163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7163
  have eq15100 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq244
       have i₂ := eq646 X0 x y
       grind)
    | exact superpose eq646 eq244
    | (have j1 := eq646 (σ x) x (σ y)
       grind)
    | exact resolve eq244 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq646
  have eq15104 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq15100 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15100
  have eq15279 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (k (τ X0) (τ X0))
       have i₂ := eq281 (τ X0)
       grind)
    | exact superpose eq281 eq16
    | (have j1 := eq281 (τ X0)
       grind)
    | exact resolve eq16 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq15313 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15279 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq15279
    | (have j0 := eq15279 X0
       grind)
    | exact resolve eq15279 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15279
  have eq15331 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15313 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15313
    | (have j0 := eq15313 X0
       grind)
    | exact resolve eq15313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15313
  have eq15339 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15331 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15331
    | (have j0 := eq15331 X0
       grind)
    | exact resolve eq15331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15331
  have eq22572 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq669 (σ x) X0
       have i₂ := eq15104 X1
       grind)
    | exact superpose eq15104 eq669
    | (have j1 := eq15104 X1
       grind)
    | exact resolve eq669 eq15104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15104
  have eq22861 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22572 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq22572
    | (have j0 := eq22572 X0 X1
       grind)
    | exact resolve eq22572 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22572
  have eq24586 : ∀ X0 : G, y = (k y y) ∨ y = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq15339 y
       have i₂ := eq22861 y X0
       grind)
    | exact superpose eq22861 eq15339
    | (have j0 := eq15339 y
       have j1 := eq22861 y y
       grind)
    | exact resolve eq15339 eq22861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15339 eq22861
  have eq24818 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq24586 X0
       have j1 := eq70 y y
       grind)
    | (have r₁ := eq24586 X0
       have r₂ := eq70 y y
       grind)
    | (have r₁ := eq24586 y
       have r₂ := eq70 y y
       grind)
    | exact resolve eq24586 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq24586
  have eq24861 : y = (k y y) := by
    first
    | (have j1 := eq660 x y
       grind)
    | (have r₁ := eq24818 x
       have r₂ := eq660 x y
       grind)
    | exact resolve eq24818 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq24818
  have eq28252 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq24861
       grind)
    | exact superpose eq24861 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq24861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24861
  have eq28257 : y = (M.op y y) := by grind
  clear eq28252
  have eq28456 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq488 X0 y
       have i₂ := eq28257
       grind)
    | exact superpose eq28257 eq488
    | exact resolve eq488 eq28257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq28458 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq585 y X1 X0
       have i₂ := eq28257
       grind)
    | exact superpose eq28257 eq585
    | exact resolve eq585 eq28257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq28463 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq669 y X0
       have i₂ := eq28257
       grind)
    | exact superpose eq28257 eq669
    | exact resolve eq669 eq28257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq28257
  have eq30014 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ y = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X0 X0
       have i₂ := eq28456 X0
       grind)
    | exact superpose eq28456 eq46
    | (have j0 := eq46 X1 X0 x
       grind)
    | exact resolve eq46 eq28456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq30112 : ∀ X0 : G, y = (σ (k X0 X0)) ∨ (τ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq254 X0 X0
       have i₂ := eq28456 (σ X0)
       grind)
    | exact superpose eq28456 eq254
    | exact resolve eq254 eq28456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq31839 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq7170 (τ y)
       have i₂ := eq28463 (τ y)
       grind)
    | exact superpose eq28463 eq7170
    | (have j0 := eq7170 (τ y)
       grind)
    | (have r₁ := eq7170 (τ y)
       have r₂ := eq28463 (τ y)
       grind)
    | exact resolve eq7170 eq28463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7170 eq28463
  have eq31861 : (τ y) = (M.op (τ y) (τ y)) := by grind
  clear eq31839
  have eq31874 : y = (τ y) := by
    first
    | (have i₁ := eq31861
       have i₂ := eq28456 (τ y)
       grind)
    | exact superpose eq28456 eq31861
    | exact resolve eq31861 eq28456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31861
  have eq33683 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq31874
       grind)
    | exact superpose eq31874 eq10
    | exact resolve eq10 eq31874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33684 : ∀ X0 : G, (k y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq31874
       grind)
    | exact superpose eq31874 eq16
    | exact resolve eq16 eq31874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34874 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33683
       grind)
    | exact superpose eq33683 eq14
    | exact resolve eq14 eq33683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76052 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq255 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq255
    | exact resolve eq255 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq76528 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76052 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq76052
    | (have j0 := eq76052 X0 X1 X2
       grind)
    | exact resolve eq76052 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq76052
  have eq76903 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k y (σ X2)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76528 X0 X1 X2
       have i₂ := eq28456 X0
       grind)
    | exact superpose eq28456 eq76528
    | (have j0 := eq76528 X0 X1 X2
       grind)
    | exact resolve eq76528 eq28456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76528
  have eq77150 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (σ (k y X2)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76903 X0 X1 X2
       have i₂ := eq33684 X2
       grind)
    | exact superpose eq33684 eq76903
    | (have j0 := eq76903 X0 X1 X2
       grind)
    | exact resolve eq76903 eq33684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76903
  have eq114120 : ∀ X0 : G, (k X0 X0) = (τ y) ∨ (τ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0)
       have i₂ := eq30112 X0
       grind)
    | exact superpose eq30112 eq9
    | (have j1 := eq30112 (k X0 X0)
       grind)
    | exact resolve eq9 eq30112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30112
  have eq114218 : ∀ X0 : G, y = (k X0 X0) ∨ (τ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq114120 X0
       have i₂ := eq31874
       grind)
    | exact superpose eq31874 eq114120
    | (have j0 := eq114120 X0
       grind)
    | exact resolve eq114120 eq31874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114120
  have eq114310 : ∀ X0 : G, y = (k X0 X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq114218 X0
       have i₂ := eq31874
       grind)
    | exact superpose eq31874 eq114218
    | (have j0 := eq114218 X0
       grind)
    | exact resolve eq114218 eq31874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31874 eq114218
  have eq229127 : ∀ X0 : G, (k X0 (σ (τ X0))) = (M.op (k X0 (σ (τ X0))) (k X0 (σ (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7155 (τ X0)
       have i₂ := eq69 X0 (τ X0)
       grind)
    | exact superpose eq69 eq7155
    | (have j1 := eq69 X0 (τ X0)
       grind)
    | exact resolve eq7155 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq7155
  have eq229359 : ∀ X0 : G, y = (k X0 (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq229127 X0
       have i₂ := eq28456 (k X0 (σ (τ X0)))
       grind)
    | exact superpose eq28456 eq229127
    | (have j0 := eq229127 X0
       grind)
    | exact resolve eq229127 eq28456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28456 eq229127
  have eq229477 : ∀ X0 : G, y = (k X0 X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq229359 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq229359
    | (have j0 := eq229359 X0
       grind)
    | exact resolve eq229359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229359
  have eq229534 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq229477 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq229477
    | (have j0 := eq229477 X0
       grind)
    | exact resolve eq229477 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229477
  have eq229642 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq229534 X0
       grind)
    | exact superpose eq229534 eq10
    | (have j1 := eq229534 X0
       grind)
    | exact resolve eq10 eq229534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229534
  have eq229666 : ∀ X0 : G, (k X0 X0) = X0 ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq229642 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq229642
    | (have j0 := eq229642 X0
       grind)
    | exact resolve eq229642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229642
  have eq230583 : ∀ X0 : G, y ≠ X0 ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq229666 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229666
  have eq230595 : ∀ X0 : G, y = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq230583 X0
       have j1 := eq114310 X0
       grind)
    | (have r₁ := eq230583 (k X0 X0)
       have r₂ := eq114310 X0
       grind)
    | (have r₁ := eq230583 X0
       have r₂ := eq114310 X0
       grind)
    | (have r₁ := eq230583 y
       have r₂ := eq114310 y
       grind)
    | exact resolve eq230583 eq114310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114310 eq230583
  have eq368348 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (σ (k y (τ X1))) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77150 X2 (τ X0) (τ X1)
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq77150
    | (have j0 := eq77150 X2 (τ X0) X2
       grind)
    | exact resolve eq77150 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq77150
  have eq368580 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ y) X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368348 X0 X1 X2
       have i₂ := eq17 X1 y
       grind)
    | exact superpose eq17 eq368348
    | (have j0 := eq368348 X0 X1 X2
       grind)
    | exact resolve eq368348 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq368348
  have eq368659 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k y X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368580 X0 X1 X2
       have i₂ := eq33683
       grind)
    | exact superpose eq33683 eq368580
    | (have j0 := eq368580 X0 X1 X2
       grind)
    | exact resolve eq368580 eq33683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33683 eq368580
  have eq368706 : ∀ X0 X1 X2 : G, (k X0 X1) = (k y X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368659 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq368659
    | (have j0 := eq368659 X0 X1 X2
       grind)
    | exact resolve eq368659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368659
  have eq368724 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (k X0 X1) = (k y X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368706 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq368706
    | (have j0 := eq368706 X0 X1 X2
       grind)
    | exact resolve eq368706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368706
  have eq477194 : ∀ X0 : G, (k X0 X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq368724 X0 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368724
  have eq477198 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq477194 X0
       have i₂ := eq230595 X0
       grind)
    | exact superpose eq230595 eq477194
    | (have j0 := eq477194 X0
       grind)
    | exact resolve eq477194 eq230595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230595 eq477194
  have eq477564 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq477198 X0
       have j1 := eq30014 y X0
       grind)
    | (have r₁ := eq477198 x
       have r₂ := eq30014 X0 x
       grind)
    | exact resolve eq477198 eq30014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30014 eq477198
  have eq478017 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq33684 X0
       have i₂ := eq477564 (σ X0)
       grind)
    | exact superpose eq477564 eq33684
    | exact resolve eq33684 eq477564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33684
  have eq478290 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq478017 X0
       have i₂ := eq477564 X0
       grind)
    | exact superpose eq477564 eq478017
    | exact resolve eq478017 eq477564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477564 eq478017
  have eq478856 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq478290 (M.op y X0)
       have i₂ := eq28458 y X0
       grind)
    | exact superpose eq28458 eq478290
    | exact resolve eq478290 eq28458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479183 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (M.op y (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq478856 X0
       have i₂ := eq478290 X0
       grind)
    | exact superpose eq478290 eq478856
    | exact resolve eq478856 eq478290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478290 eq478856
  have eq479311 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq479183 X0
       have i₂ := eq28458 y (σ X0)
       grind)
    | exact superpose eq28458 eq479183
    | exact resolve eq479183 eq28458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28458 eq479183
  have eq480373 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq34874
       have i₂ := eq479311 x
       grind)
    | exact superpose eq479311 eq34874
    | (have r₁ := eq34874
       have r₂ := eq479311 x
       grind)
    | exact resolve eq34874 eq479311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34874 eq479311
  have eq480429 : False := by grind
  exact eq480429
