import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_x_x_pyy_pyx_Equation3583 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
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
  have eq48 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X0 X0) X1) X3
       have i₂ := eq14 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq50 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq48 X0 X1 x X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X2) = (k (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq14 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 (k (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq83
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq16
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq110 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq203 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X0 X0) X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq203
  have eq255 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq217 eq111
    | exact resolve eq111 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq259 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq255
    | exact resolve eq255 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq294 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq259 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq294
  have eq298 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = X0 ∨ (M.op X0 X0) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq295 eq12
    | (have j0 := eq12 X0 (k (σ (M.op x y)) X0)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) x
       have r₂ := eq295
       grind)
    | exact resolve eq12 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq295 eq50
    | exact resolve eq50 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq302 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq298 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq420 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X2 X2) = (k (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq78 X0 X1 X2
       grind)
    | (have r₁ := eq78 X0 X1 X2
       have r₂ := eq207 X0 X1
       grind)
    | exact resolve eq78 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq421 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq420 X0 X1 X2
       have i₂ := eq207 X0 X1
       grind)
    | exact superpose eq207 eq420
    | (have j0 := eq420 X2 X2 (k (M.op X0 X1) X2)
       grind)
    | exact resolve eq420 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq506 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq421 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq421
    | (have j0 := eq421 x y X0
       grind)
    | exact resolve eq421 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (σ X2)) = (σ (k X2 X2)) ∨ (σ X2) = (k (M.op X0 X1) (σ X2)) ∨ (σ X2) = (k (M.op X0 X1) (σ X2)) ∨ (M.op X0 X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 X1
       have i₂ := eq421 X0 X1 (σ X1)
       grind)
    | exact superpose eq421 eq63
    | (have j1 := eq421 X0 X1 (σ X2)
       grind)
    | exact resolve eq63 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq664 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq665 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq664 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq674 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (σ X2)) = (σ (k X2 X2)) ∨ (σ X2) = (k (M.op X0 X1) (σ X2)) ∨ (M.op X0 X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq652 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq822 : (σ (M.op y y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq506 eq110
    | (have j1 := eq506 y
       grind)
    | exact resolve eq110 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq506
  have eq3837 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq665 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq665
    | (have j0 := eq665 (τ X0)
       grind)
    | exact resolve eq665 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq665
  have eq3850 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3837 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3837
    | (have j0 := eq3837 X0
       grind)
    | exact resolve eq3837 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3837
  have eq3857 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3850 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3850
    | (have j0 := eq3850 X0
       grind)
    | exact resolve eq3850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3850
  have eq7002 : ∀ X0 X1 : G, (σ (k (M.op x y) (M.op x y))) = (k (M.op X0 X1) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (M.op X0 X1) (σ (M.op x y))) ∨ (M.op X0 X1) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq21 eq674
    | (have j0 := eq674 X0 X1 (M.op x y)
       grind)
    | exact resolve eq674 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq7095 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k (M.op X0 X1) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (M.op X0 X1) (σ (M.op x y))) ∨ (M.op X0 X1) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq111 eq7002
    | (have j0 := eq7002 X0 X1
       grind)
    | exact resolve eq7002 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq7002
  have eq7116 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (M.op X0 X1) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (M.op X0 X1) (σ (M.op x y))) ∨ (M.op X0 X1) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq259 eq7095
    | (have j0 := eq7095 X0 X1
       grind)
    | exact resolve eq7095 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq7095
  have eq7117 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (M.op X0 X1) (σ (M.op x y))) ∨ (M.op X0 X1) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | (have j0 := eq7116 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7116
  have eq24617 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq7117
    | (have j0 := eq7117 (σ x) (σ y)
       grind)
    | exact resolve eq7117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7117
  have eq24656 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq24617
       have r₂ := eq28
       grind)
    | exact resolve eq24617 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24617
  have eq34561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq34561
    | exact resolve eq34561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34561
  have eq34567 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq34562
       have r₂ := eq28
       grind)
    | exact resolve eq34562 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34562
  have eq34573 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq34567
  have eq34846 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq34573 eq101
    | exact resolve eq101 eq34573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq34573
  have eq34870 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq34846
    | exact resolve eq34846 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34846
  have eq34873 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq3857 y
       grind)
    | (have r₁ := eq34870
       have r₂ := eq3857 y
       grind)
    | exact resolve eq34870 eq3857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3857 eq34870
  have eq34879 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq34873
  have eq34929 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq34879 eq95
    | exact resolve eq95 eq34879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq34879
  have eq34937 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq34929
  have eq35178 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq50 y y x
       have i₂ := eq34937
       grind)
    | exact superpose eq34937 eq50
    | exact resolve eq50 eq34937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq34937
  have eq35284 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35178 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35178
    | (have j0 := eq35178 x
       grind)
    | exact resolve eq35178 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35178
  have eq35372 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq822
       have i₂ := eq35284
       grind)
    | exact superpose eq35284 eq822
    | exact resolve eq822 eq35284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq35377 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq207 y X0
       have i₂ := eq35284
       grind)
    | exact superpose eq35284 eq207
    | exact resolve eq207 eq35284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq35417 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq35372
  have eq35425 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq35417
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35417
    | exact resolve eq35417 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35417
  have eq36129 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq35425 eq302
    | (have j0 := eq302 (σ y)
       grind)
    | exact resolve eq302 eq35425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq35425
  have eq36134 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq36129
  have eq36762 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36134 eq49
    | exact resolve eq49 eq36134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq36134
  have eq36799 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq36762
    | exact resolve eq36762 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36762
  have eq39880 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35284
       have i₂ := eq35377 y
       grind)
    | exact superpose eq35377 eq35284
    | exact resolve eq35284 eq35377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35284 eq35377
  have eq40008 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq39880
  have eq40038 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40008
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40008
    | exact resolve eq40008 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq40008
  have eq40055 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40038 eq30
    | exact resolve eq30 eq40038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq40038
  have eq40119 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq40055
    | exact resolve eq40055 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq40055
  have eq40120 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq40119
  have eq40132 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40120 eq21
    | exact resolve eq21 eq40120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40120
  have eq40306 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40132
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40132
    | exact resolve eq40132 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40132
  have eq40729 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40306 eq27
    | exact resolve eq27 eq40306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40306
  have eq40794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq301 eq40729
    | exact resolve eq40729 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40729
  have eq40804 : x = (M.op x y) := by
    first
    | (have r₁ := eq40794
       have r₂ := eq28
       grind)
    | exact resolve eq40794 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40794
  have eq40806 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq40804 eq21
    | exact resolve eq21 eq40804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq40981 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40806
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40806
    | exact resolve eq40806 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40806
  have eq40983 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq40981 eq27
    | exact resolve eq27 eq40981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41025 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40981 eq36799
    | exact resolve eq36799 eq40981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36799
  have eq41031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24656 eq41025
    | exact resolve eq41025 eq24656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24656 eq41025
  have eq41055 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq41031
       have r₂ := eq28
       grind)
    | exact resolve eq41031 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41031
  have eq41065 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq40804 eq41055
    | exact resolve eq41055 eq40804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40804 eq41055
  have eq41979 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq41065 eq40983
    | exact resolve eq40983 eq41065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41065
  have eq41980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq301 eq41979
    | exact resolve eq41979 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41979
  have eq42008 : x = y := by
    first
    | (have r₁ := eq41980
       have r₂ := eq28
       grind)
    | exact resolve eq41980 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41980
  have eq42054 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq42008
       grind)
    | exact superpose eq42008 eq25
    | exact resolve eq25 eq42008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq42008
  have eq42199 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq42054
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42054
    | exact resolve eq42054 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq42054
  have eq42258 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq40981 eq42199
    | exact resolve eq42199 eq40981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40981 eq42199
  have eq42421 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42258 eq40983
    | exact resolve eq40983 eq42258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40983 eq42258
  have eq42422 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq301 eq42421
    | exact resolve eq42421 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq42421
  have eq42451 : False := by grind
  exact eq42451

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_x_pxx_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  clear eq39
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
  have eq98 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 y
       grind)
    | exact resolve eq44 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq44
    | (have j0 := eq44 (M.op x y)
       grind)
    | exact resolve eq44 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq176 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op (M.op x y) x)) := by
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
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq16 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 X0 X1 x X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq192 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq181 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq181
    | (have j0 := eq181 x y X0
       grind)
    | exact resolve eq181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 x
       have i₂ := eq181 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq176 x
       have i₂ := eq181 sF0 x x
       grind)
    | exact superpose eq181 eq176
    | exact resolve eq176 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq210 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq192 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq192 (M.op x y)
       grind)
    | exact resolve eq13 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op (M.op x y) x) y)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq202
       grind)
    | exact superpose eq202 eq16
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : y ≠ (M.op (M.op x y) x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq202
       grind)
    | exact superpose eq202 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op x y) = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq219 x
       have i₂ := eq181 (M.op sF0 x) y x
       grind)
    | exact superpose eq181 eq219
    | exact resolve eq219 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq222 : (M.op x y) = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq221
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq221
    | exact resolve eq221 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq234 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq210 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq236 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq234 eq41
    | exact resolve eq41 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq237 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq236
    | exact resolve eq236 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq260 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X1 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X1 X0)
       have i₂ := eq201 X1 X0
       grind)
    | exact superpose eq201 eq13
    | (have j0 := eq13 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq201 X1 X1
       grind)
    | exact resolve eq13 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq576 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
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
  have eq578 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : (M.op x y) = (k x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq576
       have i₂ := eq202
       grind)
    | exact superpose eq202 eq576
    | exact resolve eq576 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq674 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y x) ∨ (k x y) = (M.op x x) := by
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
  clear eq18
  have eq675 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) X0) ∨ (M.op X0 (M.op x y)) = X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq192 eq12
    | (have j0 := eq12 (M.op x y) X0
       grind)
    | exact resolve eq12 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) X0) ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq680 X0
       have j1 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq680 x
       have r₂ := eq13 (M.op x y) x
       grind)
    | exact resolve eq680 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq690 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op (M.op x y) x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq674
       have i₂ := eq202
       grind)
    | exact superpose eq202 eq674
    | exact resolve eq674 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq674
  have eq936 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq682 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq944 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq237 eq936
    | (have j0 := eq936 (σ (M.op x y))
       grind)
    | (have r₁ := eq936 (σ (M.op x y))
       have r₂ := eq237
       grind)
    | exact resolve eq936 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq936
  have eq947 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq944
  have eq950 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) X0) ∨ (M.op X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq947 eq12
    | (have j0 := eq12 (σ (M.op x y)) X0
       grind)
    | exact resolve eq12 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq952 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq947 eq181
    | exact resolve eq181 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq950 X0
       have j1 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq950 x
       have r₂ := eq13 (σ (M.op x y)) x
       grind)
    | exact resolve eq950 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq968 : ∀ X0 : G, (σ (M.op x y)) ≠ X0 ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq952 eq13
    | (have j0 := eq13 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq952 (σ (M.op x y))
       grind)
    | exact resolve eq13 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3902 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq625
       grind)
    | exact superpose eq625 eq40
    | exact resolve eq40 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq3903 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3902
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3902
    | exact resolve eq3902 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3902
  have eq3906 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq3903
    | exact resolve eq3903 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3903
  have eq7066 : ∀ X0 : G, (M.op x y) ≠ (k (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq192 eq602
    | (have j0 := eq602 X0 (M.op x y)
       grind)
    | exact resolve eq602 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7072 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (M.op X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq947 eq602
    | (have j0 := eq602 X0 (σ (M.op x y))
       grind)
    | exact resolve eq602 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq947
  have eq7073 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq952 eq7072
    | (have j0 := eq7072 X0
       grind)
    | exact resolve eq7072 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7072
  have eq7079 : ∀ X0 : G, (M.op x y) ≠ (k (M.op x y) X0) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq192 eq7066
    | (have j0 := eq7066 X0
       grind)
    | exact resolve eq7066 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq7066
  have eq7827 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq260 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7904 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq7827 sF2
       grind)
    | exact superpose eq7827 eq90
    | exact resolve eq90 eq7827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq7827
  have eq7911 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq7904
    | exact resolve eq7904 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7904
  have eq16806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq3906 eq578
    | exact resolve eq578 eq3906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16815 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq16806
       have r₂ := eq27
       grind)
    | exact resolve eq16806 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16806
  have eq16823 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq16815 eq675
    | (have r₁ := eq675
       have r₂ := eq16815
       grind)
    | exact resolve eq675 eq16815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16815
  have eq16843 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq16823
  have eq16844 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq16843
  have eq16850 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq3906 eq16844
    | exact resolve eq16844 eq3906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16844
  have eq16854 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq16850
       have r₂ := eq27
       grind)
    | exact resolve eq16850 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16850
  have eq16860 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq16854 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq16854
       grind)
    | exact resolve eq13 eq16854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16865 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq16854 eq181
    | exact resolve eq181 eq16854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16866 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq16854 eq201
    | exact resolve eq201 eq16854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16854
  have eq16871 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq16860
  have eq16873 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq16866
    | exact resolve eq16866 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16866
  have eq16882 : (M.op x y) = (M.op x x) ∨ y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16865 eq16873
    | (have j1 := eq16865 (σ x)
       grind)
    | exact resolve eq16873 eq16865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16873
  have eq16893 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) ∨ y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq690
       have i₂ := eq16882
       grind)
    | exact superpose eq16882 eq690
    | (have r₁ := eq690
       have r₂ := eq16882
       grind)
    | exact resolve eq690 eq16882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16882
  have eq16913 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16893
  have eq16914 : (M.op x y) = (k x y) ∨ y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16913
  have eq18001 : (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq16871 eq3906
    | exact resolve eq3906 eq16871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3906
  have eq18004 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq16871 eq152
    | exact resolve eq152 eq16871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq16871
  have eq18008 : (M.op x y) = (M.op x x) ∨ y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18001
  have eq18012 : x = (k x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq29 eq18004
    | exact resolve eq18004 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18004
  have eq18018 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq18012
       have r₂ := eq220
       grind)
    | exact resolve eq18012 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18012
  have eq18026 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq690
       have i₂ := eq18018
       grind)
    | exact superpose eq18018 eq690
    | (have r₁ := eq690
       have r₂ := eq18018
       grind)
    | exact resolve eq690 eq18018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18038 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq201 x x
       have i₂ := eq18018
       grind)
    | exact superpose eq18018 eq201
    | exact resolve eq201 eq18018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18018
  have eq18047 : y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq18026
  have eq18052 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq18047
       have r₂ := eq220
       grind)
    | exact resolve eq18047 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq18047
  have eq18060 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x y) := by
    first
    | exact superpose eq18038 eq222
    | exact resolve eq222 eq18038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18038
  have eq18112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq18052
       grind)
    | exact superpose eq18052 eq40
    | exact resolve eq40 eq18052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18114 : x ≠ (M.op x y) ∨ x = (k x y) := by grind
  clear eq18052
  have eq18115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq18112
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18112
    | exact resolve eq18112 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18112
  have eq18119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq18115
    | exact resolve eq18115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18115
  have eq18138 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ x = (k x y) := by
    first
    | exact superpose eq18060 eq685
    | (have j0 := eq685 y
       grind)
    | (have r₁ := eq685 y
       have r₂ := eq18060
       grind)
    | exact resolve eq685 eq18060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18060
  have eq18153 : (M.op x y) = (k (M.op x y) y) ∨ x = (k x y) := by grind
  clear eq18138
  have eq18198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq18119 eq578
    | exact resolve eq578 eq18119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18210 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq18198
       have r₂ := eq27
       grind)
    | exact resolve eq18198 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18198
  have eq18219 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq18153 eq40
    | exact resolve eq40 eq18153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18153
  have eq18223 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq18219
    | exact resolve eq18219 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18219
  have eq18260 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq18223 eq7073
    | (have j0 := eq7073 (σ y)
       grind)
    | (have r₁ := eq7073 (σ y)
       have r₂ := eq18223
       grind)
    | exact resolve eq7073 eq18223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18223
  have eq18265 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by grind
  clear eq18260
  have eq18274 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) ∨ y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq690
       have i₂ := eq18008
       grind)
    | exact superpose eq18008 eq690
    | (have r₁ := eq690
       have r₂ := eq18008
       grind)
    | exact resolve eq690 eq18008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18289 : (M.op x y) ≠ (M.op x y) ∨ x = (k x (M.op x y)) ∨ y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq260 x x
       have i₂ := eq18008
       grind)
    | exact superpose eq18008 eq260
    | (have j0 := eq260 y x
       grind)
    | exact resolve eq260 eq18008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq18008
  have eq18292 : y = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18289
  have eq18295 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18274
  have eq18296 : (M.op x y) = (k x y) ∨ y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18295
  have eq18409 : (M.op x y) = (M.op y y) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18292 eq222
    | exact resolve eq222 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18416 : y ≠ (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18292 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | exact resolve eq13 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18421 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq18292 eq181
    | exact resolve eq181 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18292
  have eq18426 : y ≠ (M.op x y) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18416
  have eq18884 : y = (M.op x y) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18409
       have i₂ := eq18421 y
       grind)
    | exact superpose eq18421 eq18409
    | (have j1 := eq18421 x
       grind)
    | exact resolve eq18409 eq18421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18409 eq18421
  have eq18898 : y = (M.op x y) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18884
  have eq18906 : x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq18898
       have r₂ := eq18426
       grind)
    | exact resolve eq18898 eq18426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18426 eq18898
  have eq18932 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18906 eq41
    | exact resolve eq41 eq18906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq18906
  have eq18938 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18932
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18932
    | exact resolve eq18932 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18932
  have eq18950 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18938 eq583
    | (have j0 := eq583 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq583 (σ x) (σ (M.op x y))
       have r₂ := eq18938
       grind)
    | exact resolve eq583 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq18938
  have eq18951 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18950
  have eq18952 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have j1 := eq968 (σ x)
       grind)
    | (have r₁ := eq18951
       have r₂ := eq968 (k (σ (M.op x y)) (σ x))
       grind)
    | (have r₁ := eq18951
       have r₂ := eq968 (M.op (σ (M.op x y)) (σ x))
       grind)
    | (have r₁ := eq18951
       have r₂ := eq968 (σ x)
       grind)
    | exact resolve eq18951 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq18951
  have eq18959 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have j1 := eq957 (σ x)
       grind)
    | (have r₁ := eq18952
       have r₂ := eq957 (σ x)
       grind)
    | exact resolve eq18952 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18952
  have eq18961 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq952 eq18959
    | exact resolve eq18959 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18959
  have eq18967 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18961 eq141
    | exact resolve eq141 eq18961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18961
  have eq18973 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq28 eq18967
    | exact resolve eq18967 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18967
  have eq18984 : x = (k x (τ (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq18973 eq7911
    | exact resolve eq7911 eq18973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7911
  have eq18997 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq18973 eq201
    | exact resolve eq201 eq18973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18973
  have eq19010 : (M.op x y) = (k (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq28 eq18984
    | exact resolve eq18984 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18984
  have eq19012 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq18997 eq957
    | (have j0 := eq957 (σ x)
       grind)
    | (have r₁ := eq957 (σ x)
       have r₂ := eq18997
       grind)
    | exact resolve eq957 eq18997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq18997
  have eq19027 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq19012
  have eq19059 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq19010 eq7079
    | (have j0 := eq7079 x
       grind)
    | (have r₁ := eq7079 x
       have r₂ := eq19010
       grind)
    | exact resolve eq7079 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19010
  have eq19066 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by grind
  clear eq19059
  have eq19070 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq19066
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq19066
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq19066 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19066
  have eq19119 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq19027 eq141
    | exact resolve eq141 eq19027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq19027
  have eq19124 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq28 eq19119
    | exact resolve eq19119 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19119
  have eq19125 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq19124
  have eq19134 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq19125 eq7079
    | (have j0 := eq7079 x
       grind)
    | (have r₁ := eq7079 x
       have r₂ := eq19125
       grind)
    | exact resolve eq7079 eq19125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7079 eq19125
  have eq19140 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq19134
  have eq19173 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19140 eq222
    | exact resolve eq222 eq19140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq19246 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19173 eq685
    | (have j0 := eq685 y
       grind)
    | (have r₁ := eq685 y
       have r₂ := eq19173
       grind)
    | exact resolve eq685 eq19173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq19173
  have eq19262 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq19246
  have eq19366 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19262 eq40
    | exact resolve eq40 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq19262
  have eq19371 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq19366
    | exact resolve eq19366 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19366
  have eq19395 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19371 eq7073
    | (have j0 := eq7073 (σ y)
       grind)
    | (have r₁ := eq7073 (σ y)
       have r₂ := eq19371
       grind)
    | exact resolve eq7073 eq19371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7073 eq19371
  have eq19401 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq19395
  have eq19579 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq16865 eq19401
    | exact resolve eq19401 eq16865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16865 eq19401
  have eq19600 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq19579
  have eq19611 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19140 eq19600
    | exact resolve eq19600 eq19140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19600
  have eq20731 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq690
       have i₂ := eq19611
       grind)
    | exact superpose eq19611 eq690
    | (have r₁ := eq690
       have r₂ := eq19611
       grind)
    | exact resolve eq690 eq19611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq19611
  have eq20755 : y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20731
  have eq20760 : y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18296 eq20755
    | exact resolve eq20755 eq18296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20755
  have eq20763 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19140 eq20760
    | exact resolve eq20760 eq19140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20760
  have eq20764 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq20763
  have eq21923 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq18210 eq675
    | (have r₁ := eq675
       have r₂ := eq18210
       grind)
    | exact resolve eq675 eq18210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq18210
  have eq21954 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq21923
  have eq21955 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq21954
  have eq21964 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq18119 eq21955
    | exact resolve eq21955 eq18119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18119 eq21955
  have eq21970 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq21964
       have r₂ := eq27
       grind)
    | exact resolve eq21964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21964
  have eq21983 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq21970 eq181
    | exact resolve eq181 eq21970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq21984 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq21970 eq201
    | exact resolve eq201 eq21970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq21970
  have eq21996 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq21984
    | exact resolve eq21984 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21984
  have eq22005 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21983 eq21996
    | (have j1 := eq21983 (σ x)
       grind)
    | exact resolve eq21996 eq21983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21996
  have eq22023 : x = (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16914
       have i₂ := eq22005
       grind)
    | exact superpose eq22005 eq16914
    | exact resolve eq16914 eq22005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16914 eq22005
  have eq22034 : x = (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22023
  have eq22043 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19140 eq22034
    | exact resolve eq22034 eq19140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22034
  have eq22087 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22043 eq27
    | exact resolve eq27 eq22043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22043
  have eq22145 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq21983 eq18265
    | exact resolve eq18265 eq21983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18265 eq21983
  have eq22156 : x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22145
  have eq22191 : x = (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18296
       have i₂ := eq22156
       grind)
    | exact superpose eq22156 eq18296
    | exact resolve eq18296 eq22156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18296
  have eq22192 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20764
       have i₂ := eq22156
       grind)
    | exact superpose eq22156 eq20764
    | exact resolve eq20764 eq22156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20764 eq22156
  have eq22200 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22192
  have eq22207 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22200
       have r₂ := eq22087
       grind)
    | exact resolve eq22200 eq22087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22200
  have eq22208 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19140 eq22191
    | exact resolve eq22191 eq19140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19140 eq22191
  have eq22222 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22208
       have r₂ := eq22087
       grind)
    | exact resolve eq22208 eq22087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22208
  have eq22359 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22222 eq22087
    | exact resolve eq22087 eq22222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22087 eq22222
  have eq22360 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq22359
  have eq22373 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22360
       have r₂ := eq22207
       grind)
    | exact resolve eq22360 eq22207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22207 eq22360
  have eq22905 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq22373
       grind)
    | exact superpose eq22373 eq24
    | exact resolve eq24 eq22373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq22373
  have eq23018 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq22905
    | exact resolve eq22905 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22905
  have eq23046 : (k x (M.op x y)) = (τ (k (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23018 eq99
    | exact resolve eq99 eq23018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq23083 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23018 eq952
    | exact resolve eq952 eq23018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23189 : (k x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98 eq23046
    | exact resolve eq23046 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq23046
  have eq23211 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19070 eq23189
    | exact resolve eq23189 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19070 eq23189
  have eq23224 : x = (k x y) := by
    first
    | (have r₁ := eq23211
       have r₂ := eq18114
       grind)
    | exact resolve eq23211 eq18114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18114 eq23211
  have eq23360 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23083 eq26
    | (have j1 := eq23083 (σ x)
       grind)
    | exact resolve eq26 eq23083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23083
  have eq23392 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23360 eq27
    | exact resolve eq27 eq23360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23360
  have eq23401 : x = (M.op x y) := by
    first
    | (have r₁ := eq23392
       have r₂ := eq23018
       grind)
    | exact resolve eq23392 eq23018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23018 eq23392
  have eq23403 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq23401
       grind)
    | exact superpose eq23401 eq22
    | exact resolve eq22 eq23401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq23476 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq23224
       have i₂ := eq23401
       grind)
    | exact superpose eq23401 eq23224
    | exact resolve eq23224 eq23401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23224 eq23401
  have eq23522 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq23403 eq20
    | exact resolve eq20 eq23403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23593 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq23403 eq459
    | exact resolve eq459 eq23403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq23403
  have eq23905 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq23522 eq952
    | exact resolve eq952 eq23522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq27012 : (k (M.op x y) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq578 eq23593
    | exact resolve eq23593 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq23593
  have eq27210 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq31 eq27012
    | exact resolve eq27012 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq27012
  have eq27276 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq23476 eq27210
    | exact resolve eq27210 eq23476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23476 eq27210
  have eq27318 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq23905 eq27276
    | exact resolve eq27276 eq23905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27276
  have eq27342 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23905 eq27318
    | exact resolve eq27318 eq23905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27318
  have eq27710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27342 eq14
    | exact resolve eq14 eq27342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27342
  have eq27776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq27710
    | exact resolve eq27710 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq27710
  have eq27789 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq27776
       have r₂ := eq27
       grind)
    | exact resolve eq27776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27776
  have eq27797 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27789 eq27
    | exact resolve eq27 eq27789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27789
  have eq27817 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq27797
       have r₂ := eq23522
       grind)
    | exact resolve eq27797 eq23522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27797
  have eq27819 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27817 eq26
    | exact resolve eq26 eq27817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq27817
  have eq27988 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23905 eq27819
    | exact resolve eq27819 eq23905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23905 eq27819
  have eq28071 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq27988 eq27
    | exact resolve eq27 eq27988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq27988
  have eq28087 : False := by grind
  exact eq28087

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_x_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq54 X0 X1 x X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq65 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op (M.op X1 X0) X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq79 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq95 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq103 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq116 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq227 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
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
  have eq228 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y) X0
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X1 X0) X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq243 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by grind
  have eq249 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq227 eq243
    | exact resolve eq243 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq250 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  have eq256 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq228 eq250
    | exact resolve eq250 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq258 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq249 eq135
    | exact resolve eq135 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq249
  have eq262 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq258
    | exact resolve eq258 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq279 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
  have eq293 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq262 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq294 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq293
  have eq298 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq294 eq55
    | exact resolve eq55 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X1 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq55 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq55 eq65
    | exact resolve eq65 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq452 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq229 X0 X1
       grind)
    | exact superpose eq229 eq451
    | exact resolve eq451 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq501 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq279 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq279
    | (have j0 := eq279 X0 x
       grind)
    | exact resolve eq279 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq524 : (k (k x x) x) = (τ (k (k (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq50 eq501
    | exact resolve eq501 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq699 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq96
    | (have j0 := eq96 X0 (M.op x y)
       grind)
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq96 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq710 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq709 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq719 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq298 eq699
    | (have j0 := eq699 X0
       grind)
    | exact resolve eq699 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq725 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq298 eq719
    | (have j0 := eq719 X0
       grind)
    | exact resolve eq719 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq719
  have eq3631 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq710 (M.op X0 X1)
       have i₂ := eq452 X0 X1
       grind)
    | exact superpose eq452 eq710
    | (have j0 := eq710 (M.op X0 X1)
       grind)
    | exact resolve eq710 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq710
  have eq3645 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3631 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq3773 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq725 eq76
    | (have j1 := eq725 y
       grind)
    | exact resolve eq76 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq725
  have eq3805 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq3773
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3773
    | exact resolve eq3773 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3773
  have eq3835 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq3805
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3805
    | exact resolve eq3805 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq14034 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3835 eq95
    | exact resolve eq95 eq3835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq3835
  have eq14056 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq31 eq14034
    | exact resolve eq14034 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14034
  have eq16631 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq3645 X0 X1
       grind)
    | exact superpose eq3645 eq55
    | exact resolve eq55 eq3645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3645
  have eq17558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq17565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17558
    | exact resolve eq17558 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17558
  have eq17576 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17565
       have r₂ := eq28
       grind)
    | exact resolve eq17565 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17565
  have eq17583 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17576 eq55
    | exact resolve eq55 eq17576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17576
  have eq17604 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17583
    | (have j0 := eq17583 (σ x)
       grind)
    | exact resolve eq17583 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17583
  have eq17931 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17604 eq229
    | exact resolve eq229 eq17604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17604
  have eq17941 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17931
    | exact resolve eq17931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17931
  have eq17955 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq16631 y x x
       have i₂ := eq17941
       grind)
    | exact superpose eq17941 eq16631
    | exact resolve eq16631 eq17941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16631 eq17941
  have eq17960 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq17955 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17955
    | (have j0 := eq17955 X0
       grind)
    | exact resolve eq17955 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17955
  have eq40215 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17960 eq27
    | (have j1 := eq17960 (σ x)
       grind)
    | exact resolve eq27 eq17960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17960
  have eq40220 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40215
  have eq40248 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq229 y y
       have i₂ := eq40220
       grind)
    | exact superpose eq40220 eq229
    | exact resolve eq229 eq40220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq40220
  have eq40265 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40248
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40248
    | exact resolve eq40248 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40248
  have eq40272 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40265 eq228
    | exact resolve eq228 eq40265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40273 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40265 eq256
    | exact resolve eq256 eq40265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40265
  have eq41664 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq41678 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq40272 eq14
    | exact resolve eq14 eq40272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40272
  have eq41729 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40273 eq90
    | exact resolve eq90 eq40273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40273
  have eq41763 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq41729
    | exact resolve eq41729 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41729
  have eq43276 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq41763
       grind)
    | exact superpose eq41763 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq41763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41763
  have eq43283 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq43276
  have eq43612 : (k y y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq43614 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq55 y y x
       have i₂ := eq43283
       grind)
    | exact superpose eq43283 eq55
    | exact resolve eq55 eq43283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43283
  have eq43924 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 y X1
       have i₂ := eq43614 (M.op y X0)
       grind)
    | exact superpose eq43614 eq14
    | exact resolve eq14 eq43614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43614
  have eq46617 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41664 eq90
    | exact resolve eq90 eq41664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq41664
  have eq46942 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27 eq41678
    | (have j0 := eq41678 (σ x) X0
       grind)
    | exact resolve eq41678 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41678
  have eq50422 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq43924 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq43924
    | (have j0 := eq43924 x X0
       grind)
    | exact resolve eq43924 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43924
  have eq54074 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46942 eq46617
    | exact resolve eq46617 eq46942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46617 eq46942
  have eq54205 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq54074
  have eq54490 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43612
       have i₂ := eq54205
       grind)
    | exact superpose eq54205 eq43612
    | exact resolve eq43612 eq54205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43612 eq54205
  have eq54510 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq54490
  have eq55022 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50422 y
       have i₂ := eq54510
       grind)
    | exact superpose eq54510 eq50422
    | exact resolve eq50422 eq54510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50422 eq54510
  have eq55046 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq55022
  have eq55072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55046 eq15
    | exact resolve eq15 eq55046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55046
  have eq55214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq55072
    | exact resolve eq55072 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55072
  have eq55218 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq55214
       have r₂ := eq28
       grind)
    | exact resolve eq55214 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55214
  have eq55488 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55218 eq80
    | (have r₁ := eq80
       have r₂ := eq55218
       grind)
    | exact resolve eq80 eq55218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq55489 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq55218 eq228
    | exact resolve eq228 eq55218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq55491 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55218 eq256
    | exact resolve eq256 eq55218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq55218
  have eq55501 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq55488
  have eq55542 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq55554 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X1 (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq55489 eq14
    | exact resolve eq14 eq55489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55895 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55491 eq50
    | exact resolve eq50 eq55491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55491
  have eq55958 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq55895
    | exact resolve eq55895 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq55895
  have eq56300 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq55958
       grind)
    | exact superpose eq55958 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq55958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55958
  have eq56307 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq56300
  have eq56664 : (k x x) = (M.op x x) ∨ x = (M.op x y) := by grind
  have eq56666 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq55 x x x
       have i₂ := eq56307
       grind)
    | exact superpose eq56307 eq55
    | exact resolve eq55 eq56307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56307
  have eq57254 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x X1
       have i₂ := eq56666 (M.op x X0)
       grind)
    | exact superpose eq56666 eq14
    | exact resolve eq14 eq56666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57270 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq56666 y
       grind)
    | exact superpose eq56666 eq116
    | exact resolve eq116 eq56666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq57284 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq57270
  have eq57314 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq57284
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57284
    | exact resolve eq57284 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57284
  have eq57738 : (k (k x x) x) = (τ (k (M.op (σ x) (σ x)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55542 eq524
    | exact resolve eq524 eq55542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq55542
  have eq57815 : (τ (M.op (σ x) (σ x))) = (k (k x x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57738
       have i₂ := eq232 sF2
       grind)
    | exact superpose eq232 eq57738
    | exact resolve eq57738 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57738
  have eq58708 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq56664
       grind)
    | exact superpose eq56664 eq44
    | exact resolve eq44 eq56664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq59916 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq58708
       have i₂ := eq57254 x X0
       grind)
    | (have i₁ := eq58708
       have i₂ := eq57254 X0 x
       grind)
    | exact superpose eq57254 eq58708
    | exact resolve eq58708 eq57254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57254 eq58708
  have eq59990 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq59916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59916
  have eq60050 : ∀ X0 : G, (τ (k (σ x) (σ x))) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op X0 x)
       have i₂ := eq59990 X0
       grind)
    | exact superpose eq59990 eq16
    | exact resolve eq16 eq59990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59990
  have eq60135 : ∀ X0 : G, (k x x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq50 eq60050
    | exact resolve eq60050 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60050
  have eq60258 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (k x x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x X1
       have i₂ := eq60135 (M.op x X0)
       grind)
    | exact superpose eq60135 eq14
    | exact resolve eq14 eq60135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60135
  have eq73830 : ∀ X0 : G, x = (M.op X0 (k x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56666 x
       have i₂ := eq60258 x X0
       grind)
    | exact superpose eq60258 eq56666
    | exact resolve eq56666 eq60258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56666 eq60258
  have eq73959 : ∀ X0 : G, x = (M.op X0 (k x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq73830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73830
  have eq77401 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55501 eq85
    | exact resolve eq85 eq55501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55501
  have eq77429 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq77401
    | exact resolve eq77401 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77401
  have eq78179 : (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq77429 eq232
    | exact resolve eq232 eq77429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79025 : (τ (M.op (σ x) (σ x))) = (k (M.op x x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57815
       have i₂ := eq56664
       grind)
    | exact superpose eq56664 eq57815
    | exact resolve eq57815 eq56664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56664 eq57815
  have eq79048 : (τ (M.op (σ x) (σ x))) = (k (M.op x x) x) ∨ x = (M.op x y) := by grind
  clear eq79025
  have eq79061 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79048
       have i₂ := eq232 x
       grind)
    | exact superpose eq232 eq79048
    | exact resolve eq79048 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq79048
  have eq79077 : (τ (σ y)) = (M.op x x) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq77429 eq79061
    | exact resolve eq79061 eq77429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77429
  have eq79087 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq55554 eq79061
    | exact resolve eq79061 eq55554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55554 eq79061
  have eq79271 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq79087 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79087
  have eq79277 : (τ (σ y)) = (M.op x x) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq79077
  have eq79286 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq79277
    | exact resolve eq79277 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79277
  have eq79290 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq79286
       have r₂ := eq79
       grind)
    | exact resolve eq79286 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq79286
  have eq80256 : ∀ X0 : G, (σ (M.op x x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq79271 eq15
    | exact resolve eq15 eq79271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79271
  have eq81880 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80256 eq55489
    | exact resolve eq55489 eq80256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55489 eq80256
  have eq81963 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq81880
  have eq96859 : (τ (σ y)) = (k y x) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78179 eq85
    | exact resolve eq85 eq78179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78179
  have eq96882 : y = (k y x) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq96859
    | exact resolve eq96859 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq96859
  have eq96883 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq96882
  have eq96887 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq96883
       grind)
    | exact superpose eq96883 eq74
    | exact resolve eq74 eq96883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq96928 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96887
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq96887
    | exact resolve eq96887 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96887
  have eq102137 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq57314 eq96928
    | exact resolve eq96928 eq57314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57314 eq96928
  have eq102143 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq102137
  have eq102206 : (σ y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq81963
       have i₂ := eq102143
       grind)
    | exact superpose eq102143 eq81963
    | exact resolve eq81963 eq102143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81963 eq102143
  have eq102301 : (σ y) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq102206
  have eq102348 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq102301
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq102301
    | exact resolve eq102301 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102301
  have eq102349 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq102348
  have eq102366 : (τ (k (σ x) (σ x))) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102349 eq85
    | exact resolve eq85 eq102349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq102349
  have eq102643 : (k x x) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50 eq102366
    | exact resolve eq102366 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq102366
  have eq119204 : y = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96883
       have i₂ := eq102643
       grind)
    | exact superpose eq102643 eq96883
    | exact resolve eq96883 eq102643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96883 eq102643
  have eq119225 : y = (k x x) ∨ x = (M.op x y) := by grind
  clear eq119204
  have eq119339 : ∀ X0 : G, x = (M.op X0 y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq73959 X0
       have i₂ := eq119225
       grind)
    | exact superpose eq119225 eq73959
    | exact resolve eq73959 eq119225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73959 eq119225
  have eq119370 : ∀ X0 : G, x = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq119339 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119339
  have eq121252 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq119370 x
       grind)
    | exact superpose eq119370 eq19
    | (have j1 := eq119370 x
       grind)
    | exact resolve eq19 eq119370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq119370
  have eq121268 : x = (M.op x y) := by grind
  clear eq121252
  have eq121312 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq121268 eq21
    | exact resolve eq21 eq121268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq121352 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq121268 eq227
    | exact resolve eq227 eq121268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq121568 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq121312
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq121312
    | exact resolve eq121312 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121312
  have eq121571 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq121568 eq27
    | exact resolve eq27 eq121568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq122309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq121571 eq14056
    | exact resolve eq14056 eq121571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14056
  have eq122333 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have r₁ := eq122309
       have r₂ := eq28
       grind)
    | exact resolve eq122309 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122309
  have eq122336 : x = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq121268 eq122333
    | exact resolve eq122333 eq121268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121268 eq122333
  have eq126225 : x = y ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq79290
       have i₂ := eq122336
       grind)
    | exact superpose eq122336 eq79290
    | exact resolve eq79290 eq122336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79290 eq122336
  have eq126248 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq126225
       have i₂ := eq121352 x
       grind)
    | exact superpose eq121352 eq126225
    | exact resolve eq126225 eq121352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121352 eq126225
  have eq126249 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq126248
  have eq126475 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq126249 eq121571
    | exact resolve eq121571 eq126249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126249
  have eq126483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq294 eq126475
    | exact resolve eq126475 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126475
  have eq126563 : x = y := by
    first
    | (have r₁ := eq126483
       have r₂ := eq28
       grind)
    | exact resolve eq126483 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126483
  have eq126748 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq126563
       grind)
    | exact superpose eq126563 eq25
    | exact resolve eq25 eq126563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq126563
  have eq127076 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq126748
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq126748
    | exact resolve eq126748 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq126748
  have eq127203 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq121568 eq127076
    | exact resolve eq127076 eq121568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121568 eq127076
  have eq127531 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq127203 eq121571
    | exact resolve eq121571 eq127203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121571 eq127203
  have eq127536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq294 eq127531
    | exact resolve eq127531 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq127531
  have eq127616 : False := by grind
  exact eq127616

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq63 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq64 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq85 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq91 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 X1))) = (σ (M.op (M.op X0 X1) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (M.op X0 X1)
       have i₂ := eq86 X0 X1 (τ X2)
       grind)
    | exact superpose eq86 eq18
    | exact resolve eq18 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq94 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq94 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq94 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq94 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq105 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq101 (σ X0)
       grind)
    | exact superpose eq101 eq15
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq105
    | exact resolve eq105 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq105
  have eq146 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X0) (σ X0) x
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq64
    | exact resolve eq64 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146 (M.op X0 X1) X1
       have i₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq64 eq146
    | exact resolve eq146 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq146
  have eq234 : ∀ X0 X1 X3 : G, (M.op (σ (M.op X0 X1)) X3) = (k X3 (σ (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq86 x (σ (M.op X0 X1)) x
       have i₂ := eq173 X0 X1 x
       grind)
    | exact superpose eq173 eq86
    | exact resolve eq86 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq173
  have eq683 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq692 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq683
    | (have j0 := eq683 X0 X1
       grind)
    | exact resolve eq683 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq895 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op (τ X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X1) X0 X1
       have i₂ := eq68 (τ X1) X0
       grind)
    | exact superpose eq68 eq91
    | exact resolve eq91 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq91
  have eq920 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op (τ X1) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq895 X0 X1
       have i₂ := eq234 (τ X1) X0 X1
       grind)
    | exact superpose eq234 eq895
    | exact resolve eq895 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq895
  have eq4321 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq920 (τ X1) X1
       have i₂ := eq692 (τ X1) X1
       grind)
    | exact superpose eq692 eq920
    | (have j1 := eq692 (τ X0) X1
       grind)
    | exact resolve eq920 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq920
  have eq4379 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4321 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4321
    | (have j0 := eq4321 X0 X1
       grind)
    | exact resolve eq4321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321
  have eq4398 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4379 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4379
    | (have j0 := eq4379 X0 X1
       grind)
    | exact resolve eq4379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4379
  have eq4410 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4398 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq4398
    | (have j0 := eq4398 X0 X1
       grind)
    | exact resolve eq4398 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4398
  have eq4414 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq4410 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq4410 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq4410 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4410
  have eq4416 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4414 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4414
    | (have j0 := eq4414 X0 X1
       grind)
    | exact resolve eq4414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4414
  have eq4419 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4416 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4416
    | exact resolve eq4416 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4430 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4416 (σ X0) X1
       grind)
    | exact superpose eq4416 eq15
    | (have j1 := eq4416 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq4416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4416
  have eq4474 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq4419 X1 (τ X0)
       grind)
    | exact superpose eq4419 eq19
    | (have j1 := eq4419 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq4419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4419
  have eq4763 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4474 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4474
    | exact resolve eq4474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4474
  have eq4879 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4763 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4763
    | (have j0 := eq4763 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq4763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4763
  have eq5184 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4430 x y
       grind)
    | exact superpose eq4430 eq16
    | (have j1 := eq4430 x y
       grind)
    | exact resolve eq16 eq4430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4430
  have eq5272 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5184
       have i₂ := eq4879 x y
       grind)
    | exact superpose eq4879 eq5184
    | (have j1 := eq4879 (σ x) (σ y)
       grind)
    | (have r₁ := eq5184
       have r₂ := eq4879 x y
       grind)
    | (have r₁ := eq5184
       have r₂ := eq4879 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5184
       have r₂ := eq4879 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5184 eq4879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4879 eq5184
  have eq5273 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5272
  have eq5276 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5273
       grind)
    | exact superpose eq5273 eq16
    | exact resolve eq16 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273
  have eq5277 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5276
       have r₂ := eq116 x
       grind)
    | exact resolve eq5276 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5276
  have eq5278 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5277
       grind)
    | exact superpose eq5277 eq16
    | exact resolve eq16 eq5277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5279 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5277
       grind)
    | exact superpose eq5277 eq10
    | exact resolve eq10 eq5277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5277
  have eq5332 : x = y := by
    first
    | (have i₁ := eq5279
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5279
    | exact resolve eq5279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5279
  have eq5333 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5278
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq5278
    | exact resolve eq5278 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq5278
  have eq5337 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5333
       have i₂ := eq5332
       grind)
    | exact superpose eq5332 eq5333
    | exact resolve eq5333 eq5332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5332 eq5333
  have eq5338 : False := by grind
  exact eq5338

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyy_pyx_Equation3600 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq110 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq110
    | exact resolve eq110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq111 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq111 eq9
    | exact resolve eq9 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq123 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq117 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq117
    | exact resolve eq117 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq657 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq664 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq657
    | (have j0 := eq657 X0 X1
       grind)
    | exact resolve eq657 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq3842 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq664 x y
       grind)
    | exact superpose eq664 eq16
    | (have j1 := eq664 x y
       grind)
    | exact resolve eq16 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq15955 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq656 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq656
    | exact resolve eq656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq16098 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15955 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq15955
    | (have j0 := eq15955 X0 X1
       grind)
    | exact resolve eq15955 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955
  have eq17523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3842
       have i₂ := eq16098 x y
       grind)
    | exact superpose eq16098 eq3842
    | (have j1 := eq16098 x y
       grind)
    | (have r₁ := eq3842
       have r₂ := eq16098 x y
       grind)
    | (have r₁ := eq3842
       have r₂ := eq16098 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3842
       have r₂ := eq16098 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3842 eq16098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3842 eq16098
  have eq17524 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq17523
  have eq40064 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17524
       grind)
    | exact superpose eq17524 eq16
    | exact resolve eq16 eq17524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17524
  have eq40065 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq40064
       have r₂ := eq23 x
       grind)
    | exact resolve eq40064 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40064
  have eq40068 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq40065
       grind)
    | exact superpose eq40065 eq10
    | exact resolve eq10 eq40065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40065
  have eq40137 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq40068
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40068
    | exact resolve eq40068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40068
  have eq40140 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40137
       grind)
    | exact superpose eq40137 eq16
    | exact resolve eq16 eq40137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40137
  have eq40141 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq40140
       have r₂ := eq23 x
       grind)
    | exact resolve eq40140 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq40140
  have eq40191 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq40141
       grind)
    | exact superpose eq40141 eq10
    | exact resolve eq10 eq40141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40141
  have eq40273 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40191
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40191
    | exact resolve eq40191 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40191
  have eq40274 : x = (M.op y y) := by grind
  clear eq40273
  have eq40298 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123 y
       have i₂ := eq40274
       grind)
    | exact superpose eq40274 eq123
    | exact resolve eq123 eq40274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq40407 : x = (M.op x y) := by
    first
    | (have i₁ := eq117 y y
       have i₂ := eq40274
       grind)
    | exact superpose eq40274 eq117
    | exact resolve eq117 eq40274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq40274
  have eq41633 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40298
       grind)
    | exact superpose eq40298 eq16
    | exact resolve eq16 eq40298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40298
  have eq41739 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq41633
       have i₂ := eq40407
       grind)
    | exact superpose eq40407 eq41633
    | exact resolve eq41633 eq40407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40407 eq41633
  have eq41740 : False := by grind
  exact eq41740

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pxy_pyx_Equation3600 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq53 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op (M.op x y) x)) := by
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
  have eq54 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq56 X0 X1 x X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq104
    | exact resolve eq104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq233 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X1 X0) X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq235 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq57
  have eq11349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11349
    | exact resolve eq11349 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11349
  have eq11361 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq11350
       have r₂ := eq28
       grind)
    | exact resolve eq11350 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11350
  have eq11365 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11361
    | exact resolve eq11361 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11361
  have eq11372 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11365 eq82
    | (have r₁ := eq82
       have r₂ := eq11365
       grind)
    | exact resolve eq82 eq11365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq11396 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11365 eq233
    | exact resolve eq233 eq11365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11365
  have eq11403 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11372
  have eq11404 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11403
  have eq11405 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq235 eq11396
    | exact resolve eq11396 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq11396
  have eq13067 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11404 eq106
    | exact resolve eq106 eq11404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq11404
  have eq13081 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13067
  have eq13199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13081 eq11405
    | exact resolve eq11405 eq13081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11405 eq13081
  have eq13207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq13199
  have eq13212 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13207
       have r₂ := eq28
       grind)
    | exact resolve eq13207 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13207
  have eq13216 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq13212
       grind)
    | exact superpose eq13212 eq52
    | exact resolve eq52 eq13212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq13218 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op y x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq81
       have i₂ := eq13212
       grind)
    | exact superpose eq13212 eq81
    | (have r₁ := eq81
       have r₂ := eq13212
       grind)
    | exact resolve eq81 eq13212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq13239 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq233 x x
       have i₂ := eq13212
       grind)
    | exact superpose eq13212 eq233
    | exact resolve eq233 eq13212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq13212
  have eq13245 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op y x) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq13218
  have eq13246 : (M.op y x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13245
  have eq13249 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq234 eq13239
    | exact resolve eq13239 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq13239
  have eq13264 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq13216
    | exact resolve eq13216 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13216
  have eq13746 : (σ (M.op y x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq13246
       grind)
    | exact superpose eq13246 eq91
    | exact resolve eq91 eq13246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq13246
  have eq14661 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13746
       have i₂ := eq13249
       grind)
    | exact superpose eq13249 eq13746
    | exact resolve eq13746 eq13249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13249 eq13746
  have eq14716 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14661
  have eq14732 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq14716
    | exact resolve eq14716 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14716
  have eq14750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14732 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq14732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14732
  have eq14751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14750
  have eq14755 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq14751
    | exact resolve eq14751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14751
  have eq14767 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq14755
       have r₂ := eq28
       grind)
    | exact resolve eq14755 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14755
  have eq14771 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq14767
    | exact resolve eq14767 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14767
  have eq14863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14771 eq13264
    | exact resolve eq13264 eq14771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13264 eq14771
  have eq14890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14863
  have eq14898 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq14890
       have r₂ := eq28
       grind)
    | exact resolve eq14890 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14890
  have eq14903 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq14898 eq30
    | exact resolve eq30 eq14898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14898
  have eq15018 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq14903
    | exact resolve eq14903 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14903
  have eq15019 : x = y := by grind
  clear eq15018
  have eq15038 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15019
       grind)
    | exact superpose eq15019 eq19
    | exact resolve eq19 eq15019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15039 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15019
       grind)
    | exact superpose eq15019 eq25
    | exact resolve eq25 eq15019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15019
  have eq15136 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15039
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15039
    | exact resolve eq15039 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15039
  have eq15151 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15136 eq27
    | exact resolve eq27 eq15136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15136
  have eq15376 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15151 eq69
    | exact resolve eq69 eq15151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq15151
  have eq15424 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq15376
       have i₂ := eq15038
       grind)
    | exact superpose eq15038 eq15376
    | exact resolve eq15376 eq15038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15038 eq15376
  have eq15447 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15424 eq15
    | exact resolve eq15 eq15424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15424
  have eq15494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq15447
    | exact resolve eq15447 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq15447
  have eq15508 : False := by grind
  exact eq15508

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pxy_pyx_Equation3600 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq110 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq110
    | exact resolve eq110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (σ X0) (σ X0) x
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq111
    | exact resolve eq111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 (M.op X0 X1) X1
       have i₂ := eq111 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq111 eq112
    | exact resolve eq112 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq657 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq659 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq662 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq657
    | (have j0 := eq657 X0 X1
       grind)
    | exact resolve eq657 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq3680 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq662 x y
       grind)
    | exact superpose eq662 eq16
    | (have j1 := eq662 x y
       grind)
    | exact resolve eq16 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq8203 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq659
    | exact resolve eq659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq8316 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8203 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8203
    | (have j0 := eq8203 X0 X1
       grind)
    | exact resolve eq8203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8203
  have eq11482 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3680
       have i₂ := eq8316 y x
       grind)
    | exact superpose eq8316 eq3680
    | (have j1 := eq8316 y x
       grind)
    | (have r₁ := eq3680
       have r₂ := eq8316 y x
       grind)
    | (have r₁ := eq3680
       have r₂ := eq8316 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3680
       have r₂ := eq8316 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3680 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3680 eq8316
  have eq11483 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq11482
  have eq29374 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11483
       grind)
    | exact superpose eq11483 eq16
    | exact resolve eq16 eq11483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11483
  have eq29375 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq29374
       have r₂ := eq23 x
       grind)
    | exact resolve eq29374 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29374
  have eq29377 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29375
       grind)
    | exact superpose eq29375 eq10
    | exact resolve eq10 eq29375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29375
  have eq29431 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq29377
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29377
    | exact resolve eq29377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29377
  have eq29433 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29431
       grind)
    | exact superpose eq29431 eq16
    | exact resolve eq16 eq29431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29431
  have eq29434 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq29433
       have r₂ := eq23 x
       grind)
    | exact resolve eq29433 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29433
  have eq29465 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq29434
       grind)
    | exact superpose eq29434 eq10
    | exact resolve eq10 eq29434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29434
  have eq29528 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29465
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29465
    | exact resolve eq29465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29465
  have eq29529 : y = (M.op x x) := by grind
  clear eq29528
  have eq29645 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq111 x x x
       have i₂ := eq29529
       grind)
    | exact superpose eq29529 eq111
    | exact resolve eq111 eq29529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq29647 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq136 x x x
       have i₂ := eq29529
       grind)
    | exact superpose eq29529 eq136
    | exact resolve eq136 eq29529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq29529
  have eq30010 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29647 (σ x)
       grind)
    | exact superpose eq29647 eq16
    | exact resolve eq16 eq29647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29647
  have eq30027 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq30010
       have i₂ := eq29645 x
       grind)
    | exact superpose eq29645 eq30010
    | exact resolve eq30010 eq29645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29645 eq30010
  have eq30028 : False := by grind
  exact eq30028

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pxy_pyy_pxy_Equation3607 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq175 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op (M.op x y) X0)) := by
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
  have eq176 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op x y)) X0) x) = (M.op y (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X1 sF0) X0)
       have i₂ := eq16 X0 X1 sF0
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq975 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (k x y) := by
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
  have eq979 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
  clear eq28
  have eq986 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq986 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq986 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq986 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq989 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq987 X0
       grind)
    | exact superpose eq987 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq987 X0
       grind)
    | exact superpose eq987 eq16
    | exact resolve eq16 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op (M.op x x) X0)) ∨ (M.op x y) = (k x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq975
       grind)
    | exact superpose eq975 eq16
    | exact resolve eq16 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1045 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (M.op x y) = (k x y) := by
    intro X0
    first
    | (have i₁ := eq1043 X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1043
    | exact resolve eq1043 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1060 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq979 eq16
    | exact resolve eq16 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1062 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1060 X0
       have i₂ := eq16 X0 sF2 sF2
       grind)
    | exact superpose eq16 eq1060
    | exact resolve eq1060 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1090 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1045 x
       grind)
    | exact superpose eq1045 eq18
    | (have j1 := eq1045 x
       grind)
    | exact resolve eq18 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1045
  have eq1098 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1090
       have i₂ := eq987 x
       grind)
    | exact superpose eq987 eq1090
    | exact resolve eq1090 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1098
       grind)
    | exact superpose eq1098 eq41
    | exact resolve eq41 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1118
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1118
    | exact resolve eq1118 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20 eq1119
    | exact resolve eq1119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1148 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq1062 eq26
    | (have j1 := eq1062 (σ x)
       grind)
    | exact resolve eq26 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1153 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1148
       have i₂ := eq987 sF2
       grind)
    | exact superpose eq987 eq1148
    | exact resolve eq1148 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1153 eq1121
    | exact resolve eq1121 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1180 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq1174
       have r₂ := eq27
       grind)
    | exact resolve eq1174 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1186 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq1180 eq990
    | exact resolve eq990 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1203 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq1062 eq1186
    | exact resolve eq1186 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1206 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (σ x)) X1)) = (M.op X1 (σ x)) ∨ (M.op x y) = (k x x) := by
    intro X0 X1
    first
    | exact superpose eq1186 eq16
    | exact resolve eq16 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ x)) ∨ (M.op x y) = (k x x) := by
    intro X1
    first
    | exact superpose eq182 eq1206
    | exact resolve eq1206 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1206
  have eq1210 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1121 eq1203
    | exact resolve eq1203 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1216 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq1210
       have r₂ := eq27
       grind)
    | exact resolve eq1210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1217 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1186 eq1216
    | exact resolve eq1216 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186 eq1216
  have eq1218 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1217
       have i₂ := eq987 sF2
       grind)
    | exact superpose eq987 eq1217
    | exact resolve eq1217 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1219 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1180 eq1218
    | exact resolve eq1218 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1224 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1219 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1229 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1224
       have i₂ := eq987 sF2
       grind)
    | exact superpose eq987 eq1224
    | exact resolve eq1224 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1235 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq1229
       have r₂ := eq1180
       grind)
    | exact resolve eq1229 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq1229
  have eq1238 : (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1235
       have i₂ := eq987 sF3
       grind)
    | exact superpose eq987 eq1235
    | exact resolve eq1235 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1239 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1238
       have i₂ := eq987 sF3
       grind)
    | exact superpose eq987 eq1238
    | exact resolve eq1238 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1240 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1121 eq1239
    | exact resolve eq1239 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1244 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1207 eq987
    | exact resolve eq987 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1277 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1219 eq1244
    | exact resolve eq1244 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq1244
  have eq1432 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq1240 eq989
    | (have j0 := eq989 (σ y) X0
       grind)
    | (have r₁ := eq989 (σ y) x
       have r₂ := eq1240
       grind)
    | exact resolve eq989 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1435 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | (have j0 := eq1432 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1441 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq1277 eq1435
    | (have j0 := eq1435 X0
       grind)
    | exact resolve eq1435 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq1435
  have eq1448 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | (have j0 := eq1441 X0
       grind)
    | (have r₁ := eq1441 X0
       have r₂ := eq27
       grind)
    | exact resolve eq1441 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq1875 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1448 eq26
    | (have j1 := eq1448 (σ x)
       grind)
    | exact resolve eq26 eq1448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1448
  have eq1890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1121 eq1875
    | exact resolve eq1875 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121 eq1875
  have eq1916 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq1890
       have r₂ := eq27
       grind)
    | exact resolve eq1890 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890
  have eq1929 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1916
       grind)
    | exact superpose eq1916 eq40
    | exact resolve eq40 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1931 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq990 x X0
       have i₂ := eq1916
       grind)
    | exact superpose eq1916 eq990
    | exact resolve eq990 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1932 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1929
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1929
    | exact resolve eq1929 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929
  have eq1934 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq1932
    | exact resolve eq1932 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq1948 : (M.op (M.op x y) x) = (M.op x (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1931 sF0
       have i₂ := eq987 sF0
       grind)
    | exact superpose eq987 eq1931
    | exact resolve eq1931 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1950 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op x y)) X0) x) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1931 (M.op (M.op X1 sF0) X0)
       have i₂ := eq16 X0 X1 sF0
       grind)
    | exact superpose eq16 eq1931
    | exact resolve eq1931 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq2174 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1950 eq179
    | exact resolve eq179 eq1950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1950
  have eq2267 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op (M.op X0 X1) (M.op (M.op x (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 y (M.op X0 X1)
       have i₂ := eq2174 X0 X1
       grind)
    | exact superpose eq2174 eq16
    | exact resolve eq16 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2276 : ∀ X2 : G, (M.op X2 y) = (M.op X2 x) := by
    intro X2
    first
    | (have i₁ := eq2267 x x X2
       have i₂ := eq16 X2 x (M.op x x)
       grind)
    | exact superpose eq16 eq2267
    | exact resolve eq2267 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq2333 : (k y y) = (M.op y x) := by
    first
    | (have i₁ := eq987 y
       have i₂ := eq2276 y
       grind)
    | exact superpose eq2276 eq987
    | exact resolve eq987 eq2276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2359 : (M.op y x) = (M.op y (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq2276 sF0
       grind)
    | exact superpose eq2276 eq175
    | exact resolve eq175 eq2276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2369 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq175 eq2359
    | exact resolve eq2359 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2359
  have eq2396 : (k y y) = (M.op x x) := by
    first
    | (have i₁ := eq2369
       have i₂ := eq2333
       grind)
    | exact superpose eq2333 eq2369
    | exact resolve eq2369 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369
  have eq2411 : (k x x) = (k y y) := by
    first
    | (have i₁ := eq2396
       have i₂ := eq987 x
       grind)
    | exact superpose eq987 eq2396
    | exact resolve eq2396 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396
  have eq2418 : (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq2411
       have i₂ := eq1916
       grind)
    | exact superpose eq1916 eq2411
    | exact resolve eq2411 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq2453 : (k y y) ≠ (M.op x x) ∨ y = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2333
       grind)
    | exact superpose eq2333 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333
  have eq2463 : (k x x) ≠ (k y y) ∨ y = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq2453
       have i₂ := eq987 x
       grind)
    | exact superpose eq987 eq2453
    | exact resolve eq2453 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453
  have eq2469 : (M.op x y) ≠ (k x x) ∨ y = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq2463
       have i₂ := eq2418
       grind)
    | exact superpose eq2418 eq2463
    | exact resolve eq2463 eq2418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463
  have eq2474 : y = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have r₁ := eq2469
       have r₂ := eq1916
       grind)
    | exact resolve eq2469 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916 eq2469
  have eq2477 : y = (k y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq2474
       have i₂ := eq987 y
       grind)
    | exact superpose eq987 eq2474
    | exact resolve eq2474 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq2478 : y = (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq2477
       have i₂ := eq2418
       grind)
    | exact superpose eq2418 eq2477
    | exact resolve eq2477 eq2418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477
  have eq2479 : (k x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2478
       have i₂ := eq987 y
       grind)
    | exact superpose eq987 eq2478
    | exact resolve eq2478 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq2480 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2479
       have i₂ := eq2418
       grind)
    | exact superpose eq2418 eq2479
    | exact resolve eq2479 eq2418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2910 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq2480
       grind)
    | exact superpose eq2480 eq41
    | exact resolve eq41 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2480
  have eq2912 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2910
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2910
    | exact resolve eq2910 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2910
  have eq2914 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2912
    | exact resolve eq2912 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2912
  have eq2917 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2914 eq1153
    | exact resolve eq1153 eq2914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2914
  have eq2926 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2917
       have r₂ := eq27
       grind)
    | exact resolve eq2917 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917
  have eq2931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1934 eq2926
    | exact resolve eq2926 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq2934 : y = (M.op x y) := by
    first
    | (have r₁ := eq2931
       have r₂ := eq27
       grind)
    | exact resolve eq2931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931
  have eq2937 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2934
       grind)
    | exact superpose eq2934 eq24
    | exact resolve eq24 eq2934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2949 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2276 X0
       have i₂ := eq2934
       grind)
    | exact superpose eq2934 eq2276
    | exact resolve eq2276 eq2934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276
  have eq2953 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2418
       have i₂ := eq2934
       grind)
    | exact superpose eq2934 eq2418
    | exact resolve eq2418 eq2934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418 eq2934
  have eq2962 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2937 eq20
    | exact resolve eq20 eq2937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2937
  have eq3413 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq2953 eq1948
    | exact resolve eq1948 eq2953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq3417 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2953 eq989
    | (have j0 := eq989 (M.op x y) X0
       grind)
    | (have r₁ := eq989 (M.op x y) x
       have r₂ := eq2953
       grind)
    | exact resolve eq989 eq2953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq3419 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq3417 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3417
  have eq3423 : (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3419 eq3413
    | exact resolve eq3413 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3413 eq3419
  have eq3427 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3423
       have i₂ := eq2949 sF0
       grind)
    | exact superpose eq2949 eq3423
    | exact resolve eq3423 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2949 eq3423
  have eq3430 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3427
       have i₂ := eq987 sF0
       grind)
    | exact superpose eq987 eq3427
    | exact resolve eq3427 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987 eq3427
  have eq3432 : (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq2953 eq3430
    | exact resolve eq3430 eq2953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2953 eq3430
  have eq3454 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3432 eq36
    | exact resolve eq36 eq3432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3432
  have eq3458 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3454
    | exact resolve eq3454 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3454
  have eq3460 : (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2962 eq3458
    | exact resolve eq3458 eq2962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458
  have eq3509 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3460 eq1153
    | exact resolve eq1153 eq3460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153 eq3460
  have eq3519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1934 eq3509
    | exact resolve eq3509 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934 eq3509
  have eq3525 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3519
       have r₂ := eq27
       grind)
    | exact resolve eq3519 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3519
  have eq3532 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq3525 eq27
    | exact resolve eq27 eq3525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3525
  have eq3547 : False := by grind
  exact eq3547
