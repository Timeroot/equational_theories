import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyx_pxy_Equation3081 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X0 X2
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) X1 X0
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq81
    | exact resolve eq81 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq91 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq101 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq130 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq215 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq223 : (M.op x y) ≠ (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq215 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq215
       grind)
    | exact resolve eq13 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq224 : x = (k (M.op x y) x) := by grind
  clear eq223
  have eq227 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq224 eq130
    | exact resolve eq130 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq224
  have eq231 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq227
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq227
    | exact resolve eq227 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq234 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq231 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq234
  have eq239 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq247 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq239 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq239
       grind)
    | exact resolve eq13 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq247
  have eq262 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) X2
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq268 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq269 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq262 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq402 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ x) X0 (σ y)
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq59 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq69 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq922 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq926 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq912 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq929 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq926 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq926 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq926 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq926 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq940 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq929
    | (have j0 := eq929 X0 X1
       grind)
    | exact resolve eq929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq1112 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq235 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq235
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op x y))
       have r₂ := eq235
       grind)
    | exact resolve eq12 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq1123 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq1112
  have eq1124 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq1123
  have eq1125 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq231 eq1124
    | exact resolve eq1124 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq1124
  have eq1163 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  have eq1287 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (M.op (M.op X0 X1) X0) X0 X2
       have i₂ := eq418 X0 X1 X0
       grind)
    | exact superpose eq418 eq59
    | exact resolve eq59 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq418
  have eq1736 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) X0) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq402 eq268
    | exact resolve eq268 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq1743 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1125 eq1736
    | exact resolve eq1736 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq1736
  have eq15281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq15282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq15281
    | exact resolve eq15281 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15281
  have eq15293 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq15282
       have r₂ := eq27
       grind)
    | exact resolve eq15282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15282
  have eq15296 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq15293
    | exact resolve eq15293 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15293
  have eq15308 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15296 eq268
    | exact resolve eq268 eq15296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15296
  have eq15650 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15308 eq55
    | exact resolve eq55 eq15308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq15308
  have eq15677 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq15650
    | exact resolve eq15650 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650
  have eq15680 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq15677
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq15677
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq15677
       have r₂ := eq13 x y
       grind)
    | exact resolve eq15677 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15677
  have eq15691 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq922 x y
       have i₂ := eq15680
       grind)
    | exact superpose eq15680 eq922
    | (have j0 := eq922 x y
       grind)
    | exact resolve eq922 eq15680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15693 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15680
       grind)
    | exact superpose eq15680 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15680
  have eq15694 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15693
  have eq15696 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15691
  have eq15700 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15694
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15694
    | exact resolve eq15694 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15694
  have eq15701 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15700
  have eq15703 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15696
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15696
    | exact resolve eq15696 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15696
  have eq15716 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15703
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15703
    | exact resolve eq15703 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15703
  have eq15720 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15716
    | exact resolve eq15716 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15716
  have eq15721 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq15720
  have eq15726 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15721
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15721
    | exact resolve eq15721 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15721
  have eq15730 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15726
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15726
    | exact resolve eq15726 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15726
  have eq15743 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq269 y x
       have i₂ := eq15701
       grind)
    | exact superpose eq15701 eq269
    | exact resolve eq269 eq15701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15701
  have eq15773 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15743
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15743
    | exact resolve eq15743 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15743
  have eq15776 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15773
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15773
    | exact resolve eq15773 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15773
  have eq15777 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15776
  have eq16118 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15730 eq269
    | exact resolve eq269 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15730
  have eq16149 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16118
    | exact resolve eq16118 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16118
  have eq16152 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16149
    | exact resolve eq16149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16149
  have eq16153 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16152
  have eq16156 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq15777
       grind)
    | exact superpose eq15777 eq91
    | exact resolve eq91 eq15777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq15777
  have eq16178 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16156
    | exact resolve eq16156 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16156
  have eq17483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16178 eq16153
    | exact resolve eq16153 eq16178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16153 eq16178
  have eq17490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17483
  have eq17492 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17490
       have r₂ := eq27
       grind)
    | exact resolve eq17490 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17490
  have eq17710 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17492 eq248
    | exact resolve eq248 eq17492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq17492
  have eq17989 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17710 eq101
    | exact resolve eq101 eq17710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq17710
  have eq18021 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq17989
    | exact resolve eq17989 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17989
  have eq18024 : x = (k y x) := by
    first
    | (have r₁ := eq18021
       have r₂ := eq50
       grind)
    | exact resolve eq18021 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq18021
  have eq18037 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq940 y x
       have i₂ := eq18024
       grind)
    | exact superpose eq18024 eq940
    | (have j0 := eq940 y x
       grind)
    | exact resolve eq940 eq18024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq18038 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq922 y x
       have i₂ := eq18024
       grind)
    | exact superpose eq18024 eq922
    | (have j0 := eq922 y x
       grind)
    | exact resolve eq922 eq18024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq18040 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18024
       grind)
    | exact superpose eq18024 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18041 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq18040
  have eq18043 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18038
  have eq18044 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18037
  have eq18047 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18041
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18041
    | exact resolve eq18041 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18041
  have eq18049 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18043
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18043
    | exact resolve eq18043 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18043
  have eq18050 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18044
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18044
    | exact resolve eq18044 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18044
  have eq18062 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18049
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18049
    | exact resolve eq18049 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18049
  have eq18063 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18050
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18050
    | exact resolve eq18050 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18050
  have eq18068 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq18062
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18062
    | exact resolve eq18062 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18062
  have eq18069 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18063
    | exact resolve eq18063 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18063
  have eq18073 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq18068
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18068
    | exact resolve eq18068 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18068
  have eq18074 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18069
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18069
    | exact resolve eq18069 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18069
  have eq18078 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18073
    | exact resolve eq18073 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18073
  have eq18079 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18074
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18074
    | exact resolve eq18074 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18074
  have eq18082 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18079
    | exact resolve eq18079 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18079
  have eq18121 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18082 eq27
    | exact resolve eq27 eq18082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18082
  have eq19078 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq269 y x
       have i₂ := eq18047
       grind)
    | exact superpose eq18047 eq269
    | exact resolve eq269 eq18047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq19113 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19078
       have i₂ := eq18024
       grind)
    | exact superpose eq18024 eq19078
    | exact resolve eq19078 eq18024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18024 eq19078
  have eq19116 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19113
    | exact resolve eq19113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19113
  have eq19118 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19116
    | exact resolve eq19116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19116
  have eq19119 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19118
  have eq20253 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19119 eq20
    | exact resolve eq20 eq19119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19119
  have eq20380 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20253
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20253
    | exact resolve eq20253 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20253
  have eq20572 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20380 eq26
    | exact resolve eq26 eq20380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20380 eq18121
    | (have r₁ := eq18121
       have r₂ := eq20380
       grind)
    | exact resolve eq18121 eq20380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18121
  have eq20653 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20651
  have eq21238 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18078 eq1287
    | exact resolve eq1287 eq18078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18078
  have eq21241 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq21238
    | (have j0 := eq21238 X0
       grind)
    | exact resolve eq21238 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21238
  have eq22922 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20572 eq1743
    | exact resolve eq1743 eq20572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq22985 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22922
       have r₂ := eq27
       grind)
    | exact resolve eq22922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22922
  have eq24813 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22985 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq22985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22985
  have eq24830 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq24813
  have eq27849 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20380 eq21241
    | exact resolve eq21241 eq20380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20380
  have eq27961 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq27849 X0
       grind)
    | (have r₁ := eq27849 X0
       have r₂ := eq27
       grind)
    | exact resolve eq27849 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27849
  have eq31974 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24830 eq27961
    | exact resolve eq27961 eq24830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24830 eq27961
  have eq32096 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq31974
  have eq32099 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20653 eq32096
    | exact resolve eq32096 eq20653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20653 eq32096
  have eq32167 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq32099
  have eq32996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32167 eq20572
    | exact resolve eq20572 eq32167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20572 eq32167
  have eq33067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32996
  have eq33069 : x = (M.op x y) := by
    first
    | (have r₁ := eq33067
       have r₂ := eq27
       grind)
    | exact resolve eq33067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33067
  have eq33073 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq33069 eq20
    | exact resolve eq20 eq33069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq33213 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq33073
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33073
    | exact resolve eq33073 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33073
  have eq33594 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq33213 eq26
    | exact resolve eq26 eq33213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq33616 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33213 eq239
    | exact resolve eq239 eq33213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq33676 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33213 eq1163
    | (have r₁ := eq1163
       have r₂ := eq33213
       grind)
    | exact resolve eq1163 eq33213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq33731 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq33676
  have eq36424 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq33731 eq1287
    | exact resolve eq1287 eq33731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36426 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq33731 eq36424
    | exact resolve eq36424 eq33731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36424
  have eq39902 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33594 eq36426
    | exact resolve eq36426 eq33594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36426
  have eq40102 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39902 eq21241
    | exact resolve eq21241 eq39902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21241
  have eq40113 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq39902 eq263
    | exact resolve eq263 eq39902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq39902
  have eq40192 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq33731 eq40113
    | exact resolve eq40113 eq33731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33731 eq40113
  have eq40198 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33594 eq40102
    | exact resolve eq40102 eq33594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33594 eq40102
  have eq40199 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40198
  have eq40222 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq40199 eq27
    | exact resolve eq27 eq40199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41035 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40199 eq40192
    | exact resolve eq40192 eq40199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40192
  have eq41346 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq33616 eq41035
    | exact resolve eq41035 eq33616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33616 eq41035
  have eq41472 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq40199 eq41346
    | exact resolve eq41346 eq40199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40199 eq41346
  have eq41510 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq41472 eq268
    | exact resolve eq268 eq41472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq41472
  have eq41619 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq41510 eq112
    | exact resolve eq112 eq41510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq41510
  have eq41670 : y = (k y y) := by
    first
    | exact superpose eq29 eq41619
    | exact resolve eq41619 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq41619
  have eq41693 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq41670
       grind)
    | exact superpose eq41670 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq41670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41670
  have eq41714 : y = (M.op y y) := by grind
  clear eq41693
  have eq41825 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq1287 y y X0
       have i₂ := eq41714
       grind)
    | exact superpose eq41714 eq1287
    | exact resolve eq1287 eq41714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq41827 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq41825 X0
       have i₂ := eq41714
       grind)
    | exact superpose eq41714 eq41825
    | exact resolve eq41825 eq41714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41714 eq41825
  have eq41938 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41827 x
       have i₂ := eq18047
       grind)
    | exact superpose eq18047 eq41827
    | exact resolve eq41827 eq18047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18047 eq41827
  have eq42109 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41938
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41938
    | exact resolve eq41938 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq41938
  have eq42110 : y = (M.op x y) := by grind
  clear eq42109
  have eq42125 : x = y := by
    first
    | exact superpose eq33069 eq42110
    | exact resolve eq42110 eq33069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33069 eq42110
  have eq42132 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq42125
       grind)
    | exact superpose eq42125 eq24
    | exact resolve eq24 eq42125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq42125
  have eq42276 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq42132
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42132
    | exact resolve eq42132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq42132
  have eq42337 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq33213 eq42276
    | exact resolve eq42276 eq33213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33213 eq42276
  have eq42386 : False := by grind
  exact eq42386

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pyx_pxy_Equation3081 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq45 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X1) X0 X2
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X1 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 X2) X0
       have i₂ := eq46 X2 X1
       grind)
    | exact superpose eq46 eq9
    | exact resolve eq9 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X2) X2) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op (M.op X1 X0) X2) X2)
       have i₂ := eq45 (M.op X1 X0) X2 X0
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq85 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X2 X2) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op (M.op X2 X1) X0) X2
       have i₂ := eq73 X1 X2 X0
       grind)
    | exact superpose eq73 eq73
    | exact resolve eq73 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X3) X2) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 (M.op (M.op (M.op X0 X1) X3) X2) X0 X1
       have i₂ := eq85 X2 X3 (M.op X0 X1)
       grind)
    | exact superpose eq85 eq49
    | exact resolve eq49 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq85
  have eq147 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq147 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq147 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq147 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq149 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq148 X0
       grind)
    | exact superpose eq148 eq23
    | exact resolve eq23 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq150 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq148 X0
       grind)
    | exact superpose eq148 eq15
    | exact resolve eq15 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq150 X0
       have i₂ := eq148 (σ X0)
       grind)
    | exact superpose eq148 eq150
    | exact resolve eq150 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq152 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq149 X0
       have i₂ := eq148 (τ X0)
       grind)
    | exact superpose eq148 eq149
    | exact resolve eq149 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq149
  have eq153 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq10
    | exact resolve eq10 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X2 X3) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq139 (M.op (M.op X2 X1) X0) X0 X3 X2
       have i₂ := eq73 X1 X2 X0
       grind)
    | exact superpose eq73 eq139
    | exact resolve eq139 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq412 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq412 X0 X1
       grind)
    | exact superpose eq412 eq15
    | (have j1 := eq412 X0 X1
       grind)
    | exact resolve eq15 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq414 x y
       grind)
    | exact superpose eq414 eq16
    | (have j1 := eq414 x y
       grind)
    | exact resolve eq16 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq666 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq423
       have i₂ := eq412 (σ x) (σ y)
       grind)
    | exact superpose eq412 eq423
    | (have j1 := eq412 x y
       grind)
    | (have r₁ := eq423
       have r₂ := eq412 (σ x) (σ y)
       grind)
    | exact resolve eq423 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq423
  have eq667 : (M.op y y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq666
  have eq679 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq151 y
       have i₂ := eq667
       grind)
    | exact superpose eq667 eq151
    | exact resolve eq151 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq682 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq679
       have i₂ := eq151 x
       grind)
    | exact superpose eq151 eq679
    | exact resolve eq679 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq683 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq682
  have eq693 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0
       have i₂ := eq683
       grind)
    | exact superpose eq683 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq683
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq683
       grind)
    | exact resolve eq13 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq152 (σ y)
       have i₂ := eq683
       grind)
    | exact superpose eq683 eq152
    | exact resolve eq152 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq697 : (M.op y y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq696
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq696
    | exact resolve eq696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq699 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq697
       have i₂ := eq153 x
       grind)
    | exact superpose eq153 eq697
    | exact resolve eq697 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq697
  have eq702 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op x x) X0) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq139 y y X1 X0
       have i₂ := eq699
       grind)
    | exact superpose eq699 eq139
    | exact resolve eq139 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq709 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq699
       grind)
    | exact superpose eq699 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq699
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq699
       grind)
    | exact resolve eq13 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op (M.op x X1) X0) X2) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq702 (M.op (M.op x X1) X0) X2
       have i₂ := eq172 X0 X1 x x
       grind)
    | exact superpose eq172 eq702
    | exact resolve eq702 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq702
  have eq2646 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq709 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq2652 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq2646
       grind)
    | exact superpose eq2646 eq15
    | exact resolve eq15 eq2646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2660 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2652
       grind)
    | exact superpose eq2652 eq16
    | exact resolve eq16 eq2652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652
  have eq22283 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq693 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq22287 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2660
       have i₂ := eq22283
       grind)
    | exact superpose eq22283 eq2660
    | (have r₁ := eq2660
       have r₂ := eq22283
       grind)
    | exact resolve eq2660 eq22283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660 eq22283
  have eq22291 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq22287
  have eq22341 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq152 (σ x)
       have i₂ := eq22291
       grind)
    | exact superpose eq22291 eq152
    | exact resolve eq152 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq22291
  have eq22357 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22341
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22341
    | exact resolve eq22341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22341
  have eq22358 : x = (M.op x x) := by grind
  clear eq22357
  have eq22365 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x X1) X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq727 X1 x X0
       have i₂ := eq22358
       grind)
    | exact superpose eq22358 eq727
    | exact resolve eq727 eq22358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23256 : y = (M.op y y) := by
    first
    | (have i₁ := eq727 x x y
       have i₂ := eq22365 x x
       grind)
    | exact superpose eq22365 eq727
    | exact resolve eq727 eq22365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq22365
  have eq23336 : y = (M.op x x) := by
    first
    | (have i₁ := eq699
       have i₂ := eq23256
       grind)
    | exact superpose eq23256 eq699
    | exact resolve eq699 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq23256
  have eq23342 : x = y := by
    first
    | (have i₁ := eq23336
       have i₂ := eq22358
       grind)
    | exact superpose eq22358 eq23336
    | exact resolve eq23336 eq22358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22358 eq23336
  have eq23344 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23342
       grind)
    | exact superpose eq23342 eq16
    | exact resolve eq16 eq23342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23342
  have eq23418 : False := by grind
  exact eq23418

/-- `Equation3089`: `x = (((x ◇ y) ◇ z) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_pxy_pyx_Equation3089 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3089 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3089.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq74 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) X1)
       have i₂ := eq71 (σ X0) X1
       grind)
    | exact superpose eq71 eq28
    | exact resolve eq28 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq662 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq662 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq675 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq692 : ∀ X0 X1 : G, (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq14 X0 (τ (M.op (σ X0) X1))
       grind)
    | exact superpose eq14 eq77
    | (have j1 := eq14 X0 (τ (M.op (σ X0) X1))
       grind)
    | exact resolve eq77 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq715 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq692 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq1356 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq675 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq675
    | (have j0 := eq675 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq675 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 (M.op X0 X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq675
    | (have j0 := eq675 X0 (M.op X0 X1)
       grind)
    | exact resolve eq675 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1425 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1357 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq7252 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (M.op X0 X1)) (σ X0)
       have i₂ := eq1425 X0 X1
       grind)
    | exact superpose eq1425 eq13
    | (have j0 := eq13 (σ (M.op X0 X1)) (σ X0)
       have j1 := eq1425 X0 X1
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X1)) (σ X0)
       have r₂ := eq1425 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ (M.op X0 X1))
       have r₂ := eq1425 X0 X1
       grind)
    | exact resolve eq13 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq7271 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7252
  have eq7272 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7271
  have eq7276 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ X0)) = (σ (k (M.op X0 X1) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7272 X0 X1
       have i₂ := eq15 (M.op X0 X1) X0
       grind)
    | exact superpose eq15 eq7272
    | (have j0 := eq7272 X0 X1
       grind)
    | exact resolve eq7272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7272
  have eq7306 : ∀ X0 X1 : G, (M.op (τ (M.op (σ X0) X1)) X0) = (k (τ (M.op (σ X0) X1)) X0) ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 (τ (M.op (σ X0) X1))
       have i₂ := eq715 X0 X1
       grind)
    | exact superpose eq715 eq663
    | (have j1 := eq715 X0 X1
       grind)
    | exact resolve eq663 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7354 : ∀ X0 X1 : G, (M.op (τ (M.op (σ X0) X1)) X0) = (k (τ (M.op (σ X0) X1)) X0) ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7306
  have eq8878 : ∀ X0 X1 : G, (k X1 (k X0 (τ (σ X1)))) = X1 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1 (σ X0)
       have i₂ := eq699 (σ X1) X0
       grind)
    | exact superpose eq699 eq77
    | (have j1 := eq699 (σ X1) X0
       grind)
    | exact resolve eq77 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq8938 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8878 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8878
    | (have j0 := eq8878 X1 X0
       grind)
    | exact resolve eq8878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8878
  have eq38666 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1356 x y
       grind)
    | exact superpose eq1356 eq16
    | (have j1 := eq1356 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1356 x y
       grind)
    | exact resolve eq16 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq38749 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq38666
  have eq38810 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ X0)) = (σ (k (M.op X0 X1) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7276
  have eq55717 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8938 x y
       grind)
    | exact superpose eq8938 eq16
    | (have j1 := eq8938 x y
       grind)
    | exact resolve eq16 eq8938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8938
  have eq80074 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = (τ (M.op (σ (M.op X0 X1)) (σ X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (M.op X0 X1) X0)
       have i₂ := eq38810 X0 X1
       grind)
    | exact superpose eq38810 eq10
    | (have j1 := eq38810 X0 X1
       grind)
    | exact resolve eq10 eq38810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38810
  have eq84804 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (k (M.op X0 X1) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (M.op X0 X1) (σ X0)
       have i₂ := eq80074 X0 X1
       grind)
    | exact superpose eq80074 eq77
    | (have j1 := eq80074 X0 X1
       grind)
    | exact resolve eq77 eq80074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80074
  have eq96522 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq38749
       grind)
    | exact superpose eq38749 eq77
    | exact resolve eq77 eq38749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38749
  have eq96619 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq96522
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq96522
    | exact resolve eq96522 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96522
  have eq96642 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq96619
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq96619
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq96619
       have r₂ := eq12 y x
       grind)
    | exact resolve eq96619 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96619
  have eq96679 : (τ (σ x)) = (M.op y (τ (σ x))) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq715 y (σ x)
       have i₂ := eq96642
       grind)
    | exact superpose eq96642 eq715
    | exact resolve eq715 eq96642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq96682 : (k (τ (σ x)) y) = (M.op (τ (σ x)) y) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq7354 y (σ x)
       have i₂ := eq96642
       grind)
    | exact superpose eq96642 eq7354
    | exact resolve eq7354 eq96642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7354 eq96642
  have eq96769 : (M.op x y) = (k x y) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq96682
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq96682
    | exact resolve eq96682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96682
  have eq96771 : x = (M.op y x) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq96679
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq96679
    | exact resolve eq96679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96679
  have eq96772 : x = (M.op y x) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) := by grind
  clear eq96771
  have eq96787 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq96769
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq96769
    | exact resolve eq96769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96769
  have eq96788 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq96772
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq96772
    | exact resolve eq96772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96772
  have eq96798 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq96787
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq96787
       have r₂ := eq13 x y
       grind)
    | exact resolve eq96787 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96787
  have eq96799 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq96788
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq96788
       have r₂ := eq12 y x
       grind)
    | exact resolve eq96788 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96788
  have eq96806 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq96798
       have r₂ := eq12 x y
       grind)
    | exact resolve eq96798 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96798
  have eq97040 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq96799
       grind)
    | exact superpose eq96799 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq96799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97043 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq97040
  have eq97045 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y (k x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq55717
       have i₂ := eq97043
       grind)
    | exact superpose eq97043 eq55717
    | exact resolve eq55717 eq97043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55717
  have eq97046 : ∀ X0 : G, x = (M.op (M.op (M.op y X0) y) x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq97043
       grind)
    | exact superpose eq97043 eq9
    | exact resolve eq9 eq97043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97057 : (k y x) = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq663 x y
       have i₂ := eq97043
       grind)
    | exact superpose eq97043 eq663
    | exact resolve eq663 eq97043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97043
  have eq97109 : (k y x) = (M.op y x) ∨ x = (M.op y x) := by grind
  clear eq97057
  have eq97113 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y (k x y)) ∨ x = (M.op y x) := by grind
  clear eq97045
  have eq97114 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq96799 eq97113
    | exact resolve eq97113 eq96799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96799 eq97113
  have eq97115 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq97114
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq97114
       have r₂ := eq12 y x
       grind)
    | exact resolve eq97114 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97114
  have eq97170 : y = (k y (τ (σ x))) ∨ y = (k y x) := by
    first
    | (have i₁ := eq77 y (σ x)
       have i₂ := eq97115
       grind)
    | exact superpose eq97115 eq77
    | exact resolve eq77 eq97115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97115
  have eq97264 : y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq97170
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq97170
    | exact resolve eq97170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97170
  have eq97265 : y = (k y x) := by grind
  clear eq97264
  have eq97322 : y = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq97109
       have i₂ := eq97265
       grind)
    | exact superpose eq97265 eq97109
    | exact resolve eq97109 eq97265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97109
  have eq97325 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq675 y x
       have i₂ := eq97265
       grind)
    | exact superpose eq97265 eq675
    | (have j0 := eq675 y x
       grind)
    | exact resolve eq675 eq97265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq97265
  have eq97326 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq97325
  have eq97688 : y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq63 y x
       have i₂ := eq97322
       grind)
    | exact superpose eq97322 eq63
    | exact resolve eq63 eq97322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97746 : x ≠ y ∨ x = (M.op y x) := by grind
  have eq98138 : x = (M.op (M.op y y) x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq97046 x
       have i₂ := eq97322
       grind)
    | exact superpose eq97322 eq97046
    | exact resolve eq97046 eq97322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97046 eq97322
  have eq98293 : x = (M.op (M.op y y) x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq98138
       have r₂ := eq97746
       grind)
    | exact resolve eq98138 eq97746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97746 eq98138
  have eq98300 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq97688 eq98293
    | exact resolve eq98293 eq97688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97688 eq98293
  have eq98301 : x = (M.op y x) := by grind
  clear eq98300
  have eq98304 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) x) y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq98301
       grind)
    | exact superpose eq98301 eq9
    | exact resolve eq9 eq98301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98315 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq663 y x
       have i₂ := eq98301
       grind)
    | exact superpose eq98301 eq663
    | exact resolve eq663 eq98301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98363 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (k x y)) := by
    first
    | (have i₁ := eq84804 y x
       have i₂ := eq98301
       grind)
    | exact superpose eq98301 eq84804
    | exact resolve eq84804 eq98301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84804 eq98301
  have eq99213 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k x (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98363
       grind)
    | exact superpose eq98363 eq16
    | exact resolve eq16 eq98363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98363
  have eq100109 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq97326
       grind)
    | exact superpose eq97326 eq77
    | exact resolve eq77 eq97326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100207 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq100109
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq100109
    | exact resolve eq100109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100109
  have eq100274 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq663 (σ y) (σ x)
       have i₂ := eq100207
       grind)
    | exact superpose eq100207 eq663
    | exact resolve eq663 eq100207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100207
  have eq100339 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq100274
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq100274
    | exact resolve eq100274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100274
  have eq100361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq96806 eq100339
    | exact resolve eq100339 eq96806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96806 eq100339
  have eq100374 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq100361
       have r₂ := eq16
       grind)
    | exact resolve eq100361 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100361
  have eq100399 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq100374
       grind)
    | exact superpose eq100374 eq77
    | exact resolve eq77 eq100374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq100374
  have eq100509 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq100399
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq100399
    | exact resolve eq100399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100399
  have eq100510 : x = (k x y) := by grind
  clear eq100509
  have eq100584 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98315
       have i₂ := eq100510
       grind)
    | exact superpose eq100510 eq98315
    | exact resolve eq98315 eq100510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98315
  have eq100587 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq99213
       have i₂ := eq100510
       grind)
    | exact superpose eq100510 eq99213
    | exact resolve eq99213 eq100510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99213
  have eq100723 : (σ y) ≠ (σ y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100587
       have i₂ := eq100584
       grind)
    | exact superpose eq100584 eq100587
    | exact resolve eq100587 eq100584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100584 eq100587
  have eq100724 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq100723
  have eq100738 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq100724
       grind)
    | exact superpose eq100724 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq100724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100724
  have eq100741 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq100738
  have eq100772 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63 x y
       have i₂ := eq100741
       grind)
    | exact superpose eq100741 eq63
    | exact resolve eq63 eq100741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100741
  have eq100836 : x = (M.op x x) := by grind
  clear eq100772
  have eq100851 : y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq98304 x
       have i₂ := eq100836
       grind)
    | exact superpose eq100836 eq98304
    | exact resolve eq98304 eq100836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98304
  have eq100949 : y = (M.op x y) := by
    first
    | (have i₁ := eq100851
       have i₂ := eq100836
       grind)
    | exact superpose eq100836 eq100851
    | exact resolve eq100851 eq100836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100836 eq100851
  have eq100988 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100949
       grind)
    | exact superpose eq100949 eq16
    | exact resolve eq16 eq100949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100949
  have eq101111 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq100988
       have i₂ := eq97326
       grind)
    | exact superpose eq97326 eq100988
    | (have r₁ := eq100988
       have r₂ := eq97326
       grind)
    | exact resolve eq100988 eq97326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97326
  have eq101117 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq101111
  have eq101131 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq101117
       grind)
    | exact superpose eq101117 eq9
    | exact resolve eq9 eq101117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101142 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq663 (σ y) (σ x)
       have i₂ := eq101117
       grind)
    | exact superpose eq101117 eq663
    | exact resolve eq663 eq101117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq101117
  have eq101207 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq101142
       have r₂ := eq100988
       grind)
    | exact resolve eq101142 eq100988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101142
  have eq101228 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq101207
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq101207
    | exact resolve eq101207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101207
  have eq101241 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq101228
       have i₂ := eq100510
       grind)
    | exact superpose eq100510 eq101228
    | exact resolve eq101228 eq100510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100510 eq101228
  have eq101260 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq100988
       have i₂ := eq101241
       grind)
    | exact superpose eq101241 eq100988
    | exact resolve eq100988 eq101241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100988
  have eq101286 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq63 (σ x) (σ y)
       have i₂ := eq101241
       grind)
    | exact superpose eq101241 eq63
    | exact resolve eq63 eq101241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq103585 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq101131 (σ x)
       have i₂ := eq101286
       grind)
    | exact superpose eq101286 eq101131
    | exact resolve eq101131 eq101286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101131
  have eq103759 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103585
       have i₂ := eq101286
       grind)
    | exact superpose eq101286 eq103585
    | exact resolve eq103585 eq101286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101286 eq103585
  have eq103775 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq103759
       have i₂ := eq101241
       grind)
    | exact superpose eq101241 eq103759
    | exact resolve eq103759 eq101241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101241 eq103759
  have eq103783 : False := by grind
  exact eq103783

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pyx_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq55 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq57 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq120 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq58 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq58
    | (have j0 := eq58 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq58 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq58 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq128 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq128 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq128 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq128 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq128 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq133 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq131
  have eq158 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq162 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       have j1 := eq133 X1 X0
       grind)
    | (have r₁ := eq158 X1 X1
       have r₂ := eq133 X1 X1
       grind)
    | (have r₁ := eq158 X1 X0
       have r₂ := eq133 X0 X1
       grind)
    | exact resolve eq158 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq158
  have eq533 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq162 (σ X1) (σ X0)
       grind)
    | exact superpose eq162 eq15
    | exact resolve eq15 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 X1
       have i₂ := eq162 X1 X0
       grind)
    | exact superpose eq162 eq533
    | exact resolve eq533 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq533
  have eq543 : False := by grind
  exact eq543

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_pyx_pxy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq304 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq306 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq299 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq307 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq305 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq305 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq305 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq318 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq307 (σ X0)
       grind)
    | exact superpose eq307 eq15
    | exact resolve eq15 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq307 (τ X0)
       grind)
    | exact superpose eq307 eq31
    | exact resolve eq31 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq331 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq324 X0
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq324
    | exact resolve eq324 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq337 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq318 X0
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq318
    | exact resolve eq318 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq318
  have eq402 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (τ X0) (τ X0)
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq63
    | exact resolve eq63 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq306 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq600 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq599 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq623 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq600 (τ X1) X0
       grind)
    | exact superpose eq600 eq17
    | (have j1 := eq600 (τ X1) X0
       grind)
    | exact resolve eq17 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq600
  have eq1007 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (τ X1) X0
       have i₂ := eq623 X0 X1
       grind)
    | exact superpose eq623 eq63
    | (have j1 := eq623 (τ X0) X0
       grind)
    | exact resolve eq63 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq623
  have eq1015 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1007 X0 X1
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq1007
    | (have j0 := eq1007 X0 X1
       grind)
    | exact resolve eq1007 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1138 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1015 (σ X0) X1
       have i₂ := eq337 X0
       grind)
    | exact superpose eq337 eq1015
    | (have j0 := eq1015 (σ X0) X1
       grind)
    | exact resolve eq1015 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1173 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1138 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1138
    | (have j0 := eq1138 X0 X1
       grind)
    | exact resolve eq1138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1175 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1173 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1173
    | (have j0 := eq1173 X0 X1
       grind)
    | exact resolve eq1173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1176 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1175 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1175
    | (have j0 := eq1175 X0 X1
       grind)
    | exact resolve eq1175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1177 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1176 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1176
    | (have j0 := eq1176 X0 X1
       grind)
    | exact resolve eq1176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1186 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0
       have i₂ := eq1177 X0 X1
       grind)
    | exact superpose eq1177 eq402
    | (have j1 := eq1177 (τ X0) X1
       grind)
    | exact resolve eq402 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq1177
  have eq1217 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1186 X0 X1
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq1186
    | (have j0 := eq1186 X0 X1
       grind)
    | exact resolve eq1186 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1306 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ (k (σ X0) X1)) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 (σ X0) X1
       have i₂ := eq337 X0
       grind)
    | exact superpose eq337 eq1217
    | (have j0 := eq1217 (σ X0) X1
       grind)
    | exact resolve eq1217 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq1217
  have eq1338 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k (σ X0) X1)) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1306 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1306
    | (have j0 := eq1306 X0 X1
       grind)
    | exact resolve eq1306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1340 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (M.op X1 (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1338 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1338
    | (have j0 := eq1338 X0 X1
       grind)
    | exact resolve eq1338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq1412 : ∀ X0 X1 : G, (k (σ X1) X0) = (τ (σ (M.op X0 (σ X1)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (σ X1) X0)
       have i₂ := eq1340 X1 X0
       grind)
    | exact superpose eq1340 eq10
    | (have j1 := eq1340 X1 X1
       grind)
    | exact resolve eq10 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1454 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1412 X0 X1
       have i₂ := eq10 (M.op X0 (σ X1))
       grind)
    | exact superpose eq10 eq1412
    | (have j0 := eq1412 X0 X1
       grind)
    | exact resolve eq1412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1456 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1454 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1454
    | (have j0 := eq1454 X0 (τ X0)
       grind)
    | exact resolve eq1454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1489 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1456 X0 X1
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq1456
    | (have j0 := eq1456 X0 X1
       grind)
    | exact resolve eq1456 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq1456
  have eq1500 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq1489 X0 X1
       grind)
    | exact superpose eq1489 eq11
    | (have j1 := eq1489 X0 X1
       grind)
    | exact resolve eq11 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1518 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1500 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1500
    | (have j0 := eq1500 X0 X1
       grind)
    | exact resolve eq1500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq1526 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1518 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1518 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1518 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1547 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1526 (σ X1) (σ X0)
       grind)
    | exact superpose eq1526 eq15
    | exact resolve eq15 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1574 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1547 X0 X1
       have i₂ := eq1526 X1 X0
       grind)
    | exact superpose eq1526 eq1547
    | exact resolve eq1547 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526 eq1547
  have eq2094 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1574 x y
       grind)
    | exact superpose eq1574 eq16
    | (have r₁ := eq16
       have r₂ := eq1574 x y
       grind)
    | exact resolve eq16 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq2127 : False := by grind
  exact eq2127

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pyx_y_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op (M.op X0 X3) X3) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X0 X1) X2) X2) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X2) X2 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq29
  have eq82 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X3) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X1) X2) X3
       have i₂ := eq63 X0 X1 X2
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq303 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq2146 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X4) X4) (M.op (M.op X0 X3) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op (M.op (M.op X0 X1) X2) X2) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2174 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq2175 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq303 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq303
    | (have j0 := eq303 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq303 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2649 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2146 X0 X1 (M.op X0 X1) X2 (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq2146
    | exact resolve eq2146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2662 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) X3) X4) X4) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2146 (M.op (M.op X0 X1) X0) X1 X2 X0 X4
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq2146
    | exact resolve eq2146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2717 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2649 X0 X1 (M.op X0 X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq2649
    | exact resolve eq2649 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2718 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2649 (M.op (M.op X0 X1) X0) X1 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq2649
    | exact resolve eq2649 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649
  have eq3115 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X3) X3) X4) X4) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2662 (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2) (M.op X0 X0) X3 X4
       have i₂ := eq82 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq82 eq2662
    | exact resolve eq2662 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq14345 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2175 x y
       grind)
    | exact superpose eq2175 eq16
    | (have j1 := eq2175 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2175 x y
       grind)
    | exact resolve eq16 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq14449 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq14345
  have eq38520 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq14449
  have eq38621 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38520
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq38520
    | exact resolve eq38520 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38520
  have eq38632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq38621
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq38621 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38621
  have eq38639 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq38632
       have r₂ := eq16
       grind)
    | exact resolve eq38632 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38632
  have eq38641 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38639
       grind)
    | exact superpose eq38639 eq16
    | exact resolve eq16 eq38639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38643 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq38639
       grind)
    | exact superpose eq38639 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq38639
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq38639
       grind)
    | exact resolve eq13 eq38639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38639
  have eq38713 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq38643
  have eq38728 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38713
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq38713
    | exact resolve eq38713 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38713
  have eq38730 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq38728
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq38728 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38728
  have eq38731 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq38730
       have r₂ := eq38641
       grind)
    | exact resolve eq38730 eq38641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38641 eq38730
  have eq39098 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq38731
  have eq39238 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39098
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq39098
    | exact resolve eq39098 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39098
  have eq39252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq39238
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq39238 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39238
  have eq39259 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq39252
       have r₂ := eq16
       grind)
    | exact resolve eq39252 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39252
  have eq39263 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  have eq39269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2174 y
       have i₂ := eq39259
       grind)
    | exact superpose eq39259 eq2174
    | exact resolve eq2174 eq39259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39284 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq39259
       grind)
    | exact superpose eq39259 eq9
    | exact resolve eq9 eq39259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39259
  have eq39354 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq39269
       have r₂ := eq16
       grind)
    | exact resolve eq39269 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39269
  have eq42550 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39354
  have eq42658 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42550
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq42550
    | exact resolve eq42550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42550
  have eq42669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39263 eq42658
    | exact resolve eq42658 eq39263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42658
  have eq42676 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq42669
       have r₂ := eq16
       grind)
    | exact resolve eq42669 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42669
  have eq42679 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42676
       grind)
    | exact superpose eq42676 eq16
    | exact resolve eq16 eq42676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42681 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq42676
       grind)
    | exact superpose eq42676 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq42676
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq42676
       grind)
    | exact resolve eq13 eq42676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42685 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64 (σ x) (σ y)
       have i₂ := eq42676
       grind)
    | exact superpose eq42676 eq64
    | exact resolve eq64 eq42676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42757 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq42681
  have eq42773 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42757
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq42757
    | exact resolve eq42757 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42757
  have eq42776 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39263 eq42773
    | exact resolve eq42773 eq39263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42773
  have eq42778 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq42776
       have r₂ := eq42679
       grind)
    | exact resolve eq42776 eq42679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42776
  have eq42780 : (τ (M.op (σ x) (σ x))) = (k x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq69 x
       have i₂ := eq42685
       grind)
    | exact superpose eq42685 eq69
    | exact resolve eq69 eq42685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq42918 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42780
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq42780
    | exact resolve eq42780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42780
  have eq42932 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42685 eq42918
    | exact resolve eq42918 eq42685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42685 eq42918
  have eq42935 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42932
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq42932
    | exact resolve eq42932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42932
  have eq42948 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq42935
       grind)
    | exact superpose eq42935 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq42935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42935
  have eq42949 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq42948
  have eq42971 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq42949
       grind)
    | exact superpose eq42949 eq64
    | exact resolve eq64 eq42949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq42949
  have eq43044 : x = (M.op x x) := by grind
  clear eq42971
  have eq43082 : y = (M.op (M.op x x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39284 x
       have i₂ := eq43044
       grind)
    | exact superpose eq43044 eq39284
    | exact resolve eq39284 eq43044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39284
  have eq43089 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2174 x
       have i₂ := eq43044
       grind)
    | exact superpose eq43044 eq2174
    | (have j0 := eq2174 x
       grind)
    | exact resolve eq2174 eq43044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq43134 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq2718 x x X0
       have i₂ := eq43044
       grind)
    | exact superpose eq43044 eq2718
    | exact resolve eq2718 eq43044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43176 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq43089
  have eq43199 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq43134 X0
       have i₂ := eq43044
       grind)
    | exact superpose eq43044 eq43134
    | exact resolve eq43134 eq43044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43134
  have eq43215 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq43176
       have i₂ := eq43044
       grind)
    | exact superpose eq43044 eq43176
    | exact resolve eq43176 eq43044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43176
  have eq43216 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq43215
  have eq43218 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43082
       have i₂ := eq43044
       grind)
    | exact superpose eq43044 eq43082
    | exact resolve eq43082 eq43044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43082
  have eq43375 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x X0) X1) (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2717 (M.op x X0) x x
       have i₂ := eq43199 X0
       grind)
    | exact superpose eq43199 eq2717
    | exact resolve eq2717 eq43199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717 eq43199
  have eq43445 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x X0) X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq43375 X0 X1
       have i₂ := eq43044
       grind)
    | exact superpose eq43044 eq43375
    | exact resolve eq43375 eq43044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43044 eq43375
  have eq44203 : ∀ X1 X2 : G, x = (M.op (M.op (M.op (M.op (M.op x X1) X1) X2) X2) x) := by
    intro X1 X2
    first
    | (have i₁ := eq2662 x x x X1 X2
       have i₂ := eq43445 x x
       grind)
    | exact superpose eq43445 eq2662
    | exact resolve eq2662 eq43445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662 eq43445
  have eq44459 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43218 eq39263
    | exact resolve eq39263 eq43218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39263
  have eq44463 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43218 eq42679
    | exact resolve eq42679 eq43218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42679 eq43218
  have eq47386 : ∀ X1 X2 : G, x = (M.op (M.op (M.op (M.op (M.op x X1) X1) X2) X2) x) := by
    intro X1 X2
    first
    | (have j0 := eq44203 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44203
  have eq49078 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3115 x X0 X1 x x
       have i₂ := eq47386 x x
       grind)
    | exact superpose eq47386 eq3115
    | exact resolve eq3115 eq47386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3115 eq47386
  have eq49585 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq42778
  have eq49745 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49585
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq49585
    | exact resolve eq49585 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49585
  have eq49769 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42676 eq49745
    | exact resolve eq49745 eq42676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42676 eq49745
  have eq49781 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44459 eq49769
    | exact resolve eq49769 eq44459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44459 eq49769
  have eq49787 : x = (M.op x y) := by
    first
    | (have r₁ := eq49781
       have r₂ := eq44463
       grind)
    | exact resolve eq49781 eq44463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44463 eq49781
  have eq49788 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49787
       grind)
    | exact superpose eq49787 eq16
    | exact resolve eq16 eq49787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49795 : x ≠ x ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq49787
       grind)
    | exact superpose eq49787 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq49787
       grind)
    | exact resolve eq13 eq49787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49875 : x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq49795
  have eq49954 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq303 y x
       have i₂ := eq49875
       grind)
    | exact superpose eq49875 eq303
    | (have j0 := eq303 y x
       grind)
    | exact resolve eq303 eq49875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq49957 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq49954
  have eq49959 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq49957
       have r₂ := eq49788
       grind)
    | exact resolve eq49957 eq49788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49957
  have eq51175 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq49959
  have eq51298 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51175
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq51175
    | exact resolve eq51175 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51175
  have eq51309 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq49875 eq51298
    | exact resolve eq51298 eq49875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49875 eq51298
  have eq51316 : x = (M.op y y) := by
    first
    | (have r₁ := eq51309
       have r₂ := eq49788
       grind)
    | exact resolve eq51309 eq49788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51309
  have eq51375 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq2718 y y X0
       have i₂ := eq51316
       grind)
    | exact superpose eq51316 eq2718
    | exact resolve eq2718 eq51316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718 eq51316
  have eq51442 : ∀ X0 : G, y = (M.op (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq51375 X0
       have i₂ := eq49787
       grind)
    | exact superpose eq49787 eq51375
    | exact resolve eq51375 eq49787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51375
  have eq51651 : y = (M.op x y) := by
    first
    | (have i₁ := eq49078 x y
       have i₂ := eq51442 x
       grind)
    | exact superpose eq51442 eq49078
    | exact resolve eq49078 eq51442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49078 eq51442
  have eq51862 : x = y := by
    first
    | (have i₁ := eq51651
       have i₂ := eq49787
       grind)
    | exact superpose eq49787 eq51651
    | exact resolve eq51651 eq49787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49787 eq51651
  have eq51910 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq49788
       have i₂ := eq51862
       grind)
    | exact superpose eq51862 eq49788
    | exact resolve eq49788 eq51862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49788 eq51862
  have eq51912 : False := by grind
  exact eq51912

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_x_pxy_x_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq511 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq496 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq829 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq5873 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq829 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq829 X0 X1
       grind)
    | exact superpose eq829 eq12
    | (have j1 := eq829 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq829 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq829 X0 X1
       grind)
    | exact resolve eq12 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq5897 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5873 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5873
  have eq5904 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5897 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5897
    | (have j0 := eq5897 X0 X1
       grind)
    | exact resolve eq5897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5897
  have eq5905 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5904 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5904
  have eq6601 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5905 X0 (M.op X0 X1)
       have i₂ := eq511 X0 X1
       grind)
    | exact superpose eq511 eq5905
    | (have j0 := eq5905 X0 (M.op X0 X1)
       have j1 := eq511 X0 X1
       grind)
    | exact resolve eq5905 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6607 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5905 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq5905
    | (have j0 := eq5905 (τ X1) (τ X0)
       grind)
    | exact resolve eq5905 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6698 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq6601 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6601
  have eq6716 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6607 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6607
    | (have j0 := eq6607 X0 X1
       grind)
    | exact resolve eq6607 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6607
  have eq6733 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6716 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6716
    | (have j0 := eq6716 X0 X1
       grind)
    | exact resolve eq6716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6716
  have eq6738 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6733 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6733
    | (have j0 := eq6733 X0 X1
       grind)
    | exact resolve eq6733 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6733
  have eq6743 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6738 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6738
    | (have j0 := eq6738 X0 X1
       grind)
    | exact resolve eq6738 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6738
  have eq6748 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6743 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6743
    | (have j0 := eq6743 X0 X1
       grind)
    | exact resolve eq6743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6743
  have eq6756 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6748 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq6748
    | (have j0 := eq6748 (τ X0) (τ X1)
       grind)
    | exact resolve eq6748 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq6765 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5905 X0 X1
       have i₂ := eq6748 X1 X0
       grind)
    | exact superpose eq6748 eq5905
    | (have j0 := eq5905 X0 X1
       have j1 := eq6748 (σ X1) (σ X0)
       grind)
    | exact resolve eq5905 eq6748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5905
  have eq7571 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X1 X0)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6756 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6756
  have eq7683 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ X0) (τ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7571 X0 (M.op X0 X1)
       have i₂ := eq511 X0 X1
       grind)
    | exact superpose eq511 eq7571
    | (have j0 := eq7571 X0 (M.op X0 X1)
       have j1 := eq511 X0 X1
       grind)
    | exact resolve eq7571 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq7684 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7571 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7571
    | (have j0 := eq7571 (σ X1) (σ X0)
       grind)
    | exact resolve eq7571 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7571
  have eq7712 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ X0) (τ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq7683 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7683
  have eq7736 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7684 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7684
    | (have j0 := eq7684 X0 X1
       grind)
    | exact resolve eq7684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7684
  have eq7759 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7736 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7736
    | (have j0 := eq7736 X0 X1
       grind)
    | exact resolve eq7736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7736
  have eq7776 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7759 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7759
    | (have j0 := eq7759 X0 X1
       grind)
    | exact resolve eq7759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7759
  have eq7789 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7776 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7776
    | (have j0 := eq7776 X0 X1
       grind)
    | exact resolve eq7776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7776
  have eq7806 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7789 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7789
    | (have j0 := eq7789 (σ X0) (σ X1)
       grind)
    | exact resolve eq7789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7789
  have eq25836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6765 x y
       grind)
    | exact superpose eq6765 eq16
    | (have j1 := eq6765 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6765 x y
       grind)
    | exact resolve eq16 eq6765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6765
  have eq25982 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq25836
  have eq26146 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25982
       grind)
    | exact superpose eq25982 eq16
    | exact resolve eq16 eq25982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26196 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7712 (σ x) (σ y)
       have i₂ := eq25982
       grind)
    | exact superpose eq25982 eq7712
    | exact resolve eq7712 eq25982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7712
  have eq26221 : y = (M.op (τ (σ x)) y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26196
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq26196
    | exact resolve eq26196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26196
  have eq26241 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26221
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26221
    | exact resolve eq26221 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26221
  have eq26242 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq26241
  have eq26246 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq26242
  have eq26264 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq26246
       grind)
    | exact superpose eq26246 eq12
    | exact resolve eq12 eq26246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26246
  have eq26365 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26264
       have r₂ := eq25982
       grind)
    | exact resolve eq26264 eq25982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25982 eq26264
  have eq26383 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26365
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq26365
    | exact resolve eq26365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26365
  have eq26390 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6748 eq26383
    | (have j1 := eq6748 y x
       grind)
    | exact resolve eq26383 eq6748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6748 eq26383
  have eq26394 : y = (M.op x y) := by
    first
    | (have r₁ := eq26390
       have r₂ := eq26146
       grind)
    | exact resolve eq26390 eq26146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26146 eq26390
  have eq26397 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26394
       grind)
    | exact superpose eq26394 eq16
    | exact resolve eq16 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26440 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6698 x y
       have i₂ := eq26394
       grind)
    | exact superpose eq26394 eq6698
    | exact resolve eq6698 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6698
  have eq26576 : y = (M.op y x) := by
    first
    | (have r₁ := eq26397
       have r₂ := eq26440
       grind)
    | exact resolve eq26397 eq26440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26440
  have eq26583 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq26576
       grind)
    | exact superpose eq26576 eq12
    | exact resolve eq12 eq26576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26576
  have eq26660 : y = (k y x) := by
    first
    | (have r₁ := eq26583
       have r₂ := eq26394
       grind)
    | exact resolve eq26583 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26394 eq26583
  have eq26925 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7806 y x
       have i₂ := eq26660
       grind)
    | exact superpose eq26660 eq7806
    | (have j0 := eq7806 y x
       grind)
    | exact resolve eq7806 eq26660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7806 eq26660
  have eq26928 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26925
  have eq26936 : False := by grind
  exact eq26936

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyx_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq53 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq174 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq179 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       have j1 := eq56 X1 X0
       grind)
    | (have r₁ := eq174 X1 X0
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq174 X0 X0
       have r₂ := eq56 X0 X0
       grind)
    | exact resolve eq174 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq174
  have eq451 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq179 (σ X1) (σ X0)
       grind)
    | exact superpose eq179 eq15
    | exact resolve eq15 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq179 X1 X0
       grind)
    | exact superpose eq179 eq451
    | exact resolve eq451 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq451
  have eq461 : False := by grind
  exact eq461
