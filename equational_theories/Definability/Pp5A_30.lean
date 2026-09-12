import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pxx_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq131 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq174 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 X1 X2 X3
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq182 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X1 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq182 X1
       grind)
    | exact superpose eq182 eq190
    | (have j0 := eq190 X0 X1
       grind)
    | (have r₁ := eq190 X0 X0
       have r₂ := eq182 X0
       grind)
    | exact resolve eq190 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq195 : (M.op (M.op x y) y) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq174 sF0
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq174
    | exact resolve eq174 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq206 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq175 sF4
       have i₂ := eq182 sF4
       grind)
    | exact superpose eq182 eq175
    | exact resolve eq175 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq217 : ∀ X0 : G, (M.op X0 (k (M.op x y) (M.op x y))) = (M.op X0 (M.op (M.op (M.op x y) y) X0)) := by
    intro X0
    first
    | exact superpose eq195 eq16
    | exact resolve eq16 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq218 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq217 X0
       have i₂ := eq16 X0 y sF0
       grind)
    | exact superpose eq16 eq217
    | exact resolve eq217 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq241 : ∀ X0 : G, (M.op X0 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq206 eq16
    | exact resolve eq16 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq242 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq241 X0
       have i₂ := eq16 X0 sF3 sF4
       grind)
    | exact superpose eq16 eq241
    | exact resolve eq241 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq371 : (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq242 eq182
    | exact resolve eq182 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 : G, (k (k (σ x) (σ x)) (σ X0)) = (σ (k (k x x) X0)) := by
    intro X0
    first
    | exact superpose eq97 eq34
    | exact resolve eq34 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq455 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ x))) = (σ (k X0 (k x x))) := by
    intro X0
    first
    | exact superpose eq97 eq38
    | exact resolve eq38 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq97
  have eq652 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op (k X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X2 X0 X1 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq178
    | exact resolve eq178 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 (M.op X0 X1) X1 X2 X0
       have i₂ := eq182 (M.op X0 X1)
       grind)
    | exact superpose eq182 eq178
    | exact resolve eq178 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq692 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq189
    | exact resolve eq189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq727 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1 (k X0 X0)
       have i₂ := eq182 (k X0 X0)
       grind)
    | exact superpose eq182 eq652
    | exact resolve eq652 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq869 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq928 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq901 X0 X1 X2
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq901
    | (have j0 := eq901 X0 X1 X2
       grind)
    | exact resolve eq901 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq949 : ∀ X0 X1 : G, (k X1 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq919 X0 X1
       have i₂ := eq182 X1
       grind)
    | exact superpose eq182 eq919
    | (have j0 := eq919 X0 X1
       grind)
    | exact resolve eq919 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq981 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq928 X0 X1 X2
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq928
    | (have j0 := eq928 X0 X1 X2
       grind)
    | exact resolve eq928 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1000 : ∀ X0 X1 : G, (k X1 X0) = (k X1 X1) ∨ (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq949 X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq949
    | (have j0 := eq949 X0 X1
       grind)
    | exact resolve eq949 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq1031 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1032 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1031 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq1031
    | (have j0 := eq1031 X0
       grind)
    | exact resolve eq1031 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1034 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) X0) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1032 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq1032
    | (have j0 := eq1032 X0
       grind)
    | exact resolve eq1032 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq6061 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq981 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq6062 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6061 X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq6061
    | (have j0 := eq6061 X0 X1
       grind)
    | (have r₁ := eq6061 X0 X0
       have r₂ := eq182 X0
       grind)
    | exact resolve eq6061 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6061
  have eq6113 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6062 X0 X1
       have j1 := eq1000 X1 X0
       grind)
    | (have r₁ := eq6062 X1 X0
       have r₂ := eq1000 X0 X1
       grind)
    | (have r₁ := eq6062 X0 X0
       have r₂ := eq1000 X0 X0
       grind)
    | (have r₁ := eq6062 X0 X0
       have r₂ := eq1000 X0 (k X0 X0)
       grind)
    | exact resolve eq6062 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq6062
  have eq6209 : (M.op x y) = (k x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6113 x y
       grind)
    | exact superpose eq6113 eq18
    | (have j1 := eq6113 x y
       grind)
    | exact resolve eq18 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6215 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq6113 sF2 sF3
       grind)
    | exact superpose eq6113 eq26
    | (have j1 := eq6113 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6266 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6209
       grind)
    | exact superpose eq6209 eq40
    | exact resolve eq40 eq6209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6209
  have eq6267 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq6266
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6266
    | exact resolve eq6266 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6266
  have eq6271 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq20 eq6267
    | exact resolve eq6267 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6267
  have eq6279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq6271 eq6215
    | exact resolve eq6215 eq6271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6215 eq6271
  have eq6286 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have r₁ := eq6279
       have r₂ := eq27
       grind)
    | exact resolve eq6279 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6279
  have eq6455 : (τ (σ x)) = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq6286 eq115
    | exact resolve eq115 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq6286
  have eq6466 : x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq6455
    | exact resolve eq6455 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6455
  have eq6467 : x = (k y y) := by grind
  clear eq6466
  have eq6475 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq6467
       grind)
    | exact superpose eq6467 eq40
    | exact resolve eq40 eq6467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6479 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq692 y X0
       have i₂ := eq6467
       grind)
    | exact superpose eq6467 eq692
    | exact resolve eq692 eq6467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq6480 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq652 y X0 X1
       have i₂ := eq6467
       grind)
    | exact superpose eq6467 eq652
    | exact resolve eq652 eq6467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq6482 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq6479 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6479
    | (have j0 := eq6479 X0
       grind)
    | exact resolve eq6479 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6479
  have eq6484 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq6475
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6475
    | exact resolve eq6475 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6475
  have eq6487 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq6482 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6482
    | (have j0 := eq6482 X0
       grind)
    | exact resolve eq6482 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6482
  have eq6489 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq6484
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6484
    | exact resolve eq6484 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6484
  have eq6496 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq6489 eq727
    | exact resolve eq727 eq6489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6551 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq6480 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6480
    | (have j0 := eq6480 X0 y
       grind)
    | exact resolve eq6480 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6480
  have eq6638 : (k y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq6551 y
       grind)
    | exact superpose eq6551 eq182
    | exact resolve eq182 eq6551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6639 : ∀ X0 : G, (M.op y X0) ≠ (M.op y (M.op x y)) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq6551 y
       grind)
    | exact superpose eq6551 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq6551 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq6551 y
       grind)
    | exact resolve eq13 eq6551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6655 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6551 x
       grind)
    | exact superpose eq6551 eq18
    | (have j1 := eq6551 x
       grind)
    | exact resolve eq18 eq6551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6670 : ∀ X0 : G, (M.op y X0) ≠ (M.op y (M.op x y)) ∨ (k X0 y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6639 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq6639
    | (have j0 := eq6639 X0
       grind)
    | exact resolve eq6639 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6639
  have eq6671 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq6638
       have i₂ := eq6467
       grind)
    | exact superpose eq6467 eq6638
    | exact resolve eq6638 eq6467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6638
  have eq6689 : ∀ X0 : G, (M.op X0 (k (M.op x y) (M.op x y))) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6655 eq665
    | exact resolve eq665 eq6655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6693 : (M.op x y) = (k x (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6655 eq6113
    | (have j0 := eq6113 x (M.op x y)
       grind)
    | exact resolve eq6113 eq6655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6700 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k x x)) := by
    intro X0
    first
    | exact superpose eq6671 eq665
    | exact resolve eq665 eq6671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6770 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq6487
    | (have j0 := eq6487 (σ y)
       grind)
    | exact resolve eq6487 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6487
  have eq6829 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6770
       have i₂ := eq182 sF3
       grind)
    | exact superpose eq182 eq6770
    | exact resolve eq6770 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6770
  have eq6833 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6489 eq6829
    | exact resolve eq6829 eq6489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6829
  have eq6839 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq6833 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq13 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6842 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq6833 eq665
    | exact resolve eq665 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833
  have eq6847 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq6496 eq6842
    | exact resolve eq6842 eq6496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6842
  have eq6850 : (σ x) ≠ (k (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq6839
       have i₂ := eq182 sF3
       grind)
    | exact superpose eq182 eq6839
    | exact resolve eq6839 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6839
  have eq6853 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have r₁ := eq6850
       have r₂ := eq6489
       grind)
    | exact resolve eq6850 eq6489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6489 eq6850
  have eq6854 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq6853
       have i₂ := eq182 sF4
       grind)
    | exact superpose eq182 eq6853
    | exact resolve eq6853 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6853
  have eq6864 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6847 eq182
    | exact resolve eq182 eq6847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6865 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq6847 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq6847 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq6847 (σ y)
       grind)
    | exact resolve eq13 eq6847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6867 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq6847 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq6847 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq6847 (σ y)
       grind)
    | exact resolve eq13 eq6847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6874 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (M.op (σ x) (σ y))) ∨ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq6847 eq6113
    | (have j0 := eq6113 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq6113 eq6847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6847
  have eq6893 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (M.op (σ x) (σ y))) ∨ (k (M.op (σ x) (σ y)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq6854 eq6874
    | (have j0 := eq6874 X0
       grind)
    | exact resolve eq6874 eq6854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6874
  have eq6897 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (k X0 X0) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq6867 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq6867
    | (have j0 := eq6867 X0
       grind)
    | exact resolve eq6867 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6867
  have eq6899 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq6865 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq6865
    | (have j0 := eq6865 X0
       grind)
    | exact resolve eq6865 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865
  have eq6900 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq6854 eq6864
    | exact resolve eq6864 eq6854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6864
  have eq6907 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X0) ∨ (M.op X0 (σ y)) ≠ (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6897 X0
       have i₂ := eq182 sF4
       grind)
    | exact superpose eq182 eq6897
    | (have j0 := eq6897 X0
       grind)
    | (have r₁ := eq6897 (σ y)
       have r₂ := eq182 (σ y)
       grind)
    | exact resolve eq6897 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6897
  have eq6911 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (k X0 X0) ∨ (k (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq6854 eq6907
    | (have j0 := eq6907 X0
       grind)
    | exact resolve eq6907 eq6854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6907
  have eq6914 : (M.op (k (M.op (σ x) (σ y)) (σ y)) (σ y)) = (k (k (M.op (σ x) (σ y)) (σ y)) (k (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq6854 eq371
    | exact resolve eq371 eq6854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq6915 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq6854 eq242
    | exact resolve eq242 eq6854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7025 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq6496 eq182
    | exact resolve eq182 eq6496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7487 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6693 eq35
    | exact resolve eq35 eq6693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq6693
  have eq7490 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq7487
    | exact resolve eq7487 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7487
  have eq7501 : (k x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1034 y
       have i₂ := eq6467
       grind)
    | exact superpose eq6467 eq1034
    | exact resolve eq1034 eq6467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6467
  have eq7508 : (k (k x x) x) = (M.op x (M.op x y)) ∨ (k x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1034 x
       have i₂ := eq6700 x
       grind)
    | exact superpose eq6700 eq1034
    | exact resolve eq1034 eq6700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7512 : (M.op (σ x) (σ y)) = (k (k (σ x) (σ x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6496 eq1034
    | exact resolve eq1034 eq6496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq7590 : (M.op (σ x) (σ y)) = (k (k (σ x) (σ x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq7512
    | exact resolve eq7512 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7512
  have eq7593 : (M.op x y) = (k (k x x) x) ∨ (k x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq6655 eq7508
    | exact resolve eq7508 eq6655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7508
  have eq7631 : (M.op (σ x) (σ y)) = (k (k (σ x) (σ x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq7590
    | exact resolve eq7590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7590
  have eq7634 : (M.op x y) = (k (k x x) x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq6655 eq7593
    | exact resolve eq7593 eq6655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7593
  have eq8441 : x ≠ (k x y) ∨ x = (M.op y x) := by grind
  have eq9086 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq6893 eq26
    | (have j1 := eq6893 (σ x)
       grind)
    | exact resolve eq26 eq6893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6893
  have eq9602 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq400 x
       have i₂ := eq7634
       grind)
    | exact superpose eq7634 eq400
    | exact resolve eq400 eq7634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq7634
  have eq9605 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq9602
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9602
    | exact resolve eq9602 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9602
  have eq9607 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20 eq9605
    | exact resolve eq9605 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9605
  have eq9750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq9607 eq7631
    | exact resolve eq7631 eq9607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9753 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq9750
       have r₂ := eq27
       grind)
    | exact resolve eq9750 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9750
  have eq9762 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq9753 eq9607
    | exact resolve eq9607 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9607
  have eq9769 : ∀ X0 : G, (M.op X0 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (σ x)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq9753 eq727
    | exact resolve eq727 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9772 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (k x x) := by grind
  clear eq9762
  have eq9775 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq242 eq9769
    | exact resolve eq9769 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq9769
  have eq12604 : (M.op y (M.op x y)) ≠ (M.op y (M.op x y)) ∨ (k (k x x) y) = (k (k x x) (k x x)) := by
    first
    | (have i₁ := eq6670 (k x x)
       have i₂ := eq6700 y
       grind)
    | exact superpose eq6700 eq6670
    | (have j0 := eq6670 (M.op x y)
       grind)
    | (have r₁ := eq6670 (k x x)
       have r₂ := eq6700 y
       grind)
    | exact resolve eq6670 eq6700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12632 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq6670 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6670
  have eq12638 : (k (k x x) y) = (k (k x x) (k x x)) := by grind
  clear eq12604
  have eq12729 : (k (σ (M.op x y)) (σ y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq12632 eq40
    | exact resolve eq40 eq12632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12730 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq12729
    | exact resolve eq12729 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12729
  have eq12732 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq12730
    | exact resolve eq12730 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12730
  have eq13379 : (σ (k (k x x) y)) = (k (σ (k x x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq455 (k x x)
       have i₂ := eq12638
       grind)
    | exact superpose eq12638 eq455
    | exact resolve eq455 eq12638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq12638
  have eq13395 : (σ (k (k x x) y)) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq13379
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq13379
    | exact resolve eq13379 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13379
  have eq13406 : (σ (k (k x x) y)) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq13395
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13395
    | exact resolve eq13395 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13395
  have eq13411 : (σ (k (k x x) y)) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq7025 eq13406
    | exact resolve eq13406 eq7025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13406
  have eq13415 : (k (σ (k x x)) (σ y)) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq13411
       have i₂ := eq40 (k x x)
       grind)
    | exact superpose eq40 eq13411
    | exact resolve eq13411 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq13411
  have eq13417 : (k (k (σ x) (σ x)) (σ y)) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq13415
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq13415
    | exact resolve eq13415 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13415
  have eq13419 : (k (k (σ x) (σ x)) (σ y)) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq13417
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13417
    | exact resolve eq13417 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13417
  have eq17370 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (k (k (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6496 eq6899
    | (have j0 := eq6899 (σ y)
       grind)
    | (have r₁ := eq6899 (k (σ x) (σ x))
       have r₂ := eq6496 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq6899 eq6496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6496
  have eq17372 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k (k (M.op (σ x) (σ y)) (σ y)) (k (M.op (σ x) (σ y)) (σ y))) = (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6915 eq6899
    | (have j0 := eq6899 (σ y)
       grind)
    | (have r₁ := eq6899 (k (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq6915 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq6899 eq6915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17381 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (k (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq6900 eq6899
    | (have j0 := eq6899 X0
       grind)
    | exact resolve eq6899 eq6900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6899 eq6900
  have eq17394 : (k (k (M.op (σ x) (σ y)) (σ y)) (k (M.op (σ x) (σ y)) (σ y))) = (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq17372
  have eq17396 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (k (k (σ x) (σ x)) (M.op (σ x) (σ y))) := by grind
  clear eq17370
  have eq17567 : (M.op (k (M.op (σ x) (σ y)) (σ y)) (σ y)) = (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17394 eq6914
    | exact resolve eq6914 eq17394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6914
  have eq17723 : (M.op (k (σ x) (σ x)) (σ y)) = (k (k (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17396 eq7025
    | exact resolve eq7025 eq17396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7025
  have eq17724 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (k (σ x) (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq17396 eq727
    | exact resolve eq727 eq17396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17396
  have eq17740 : (k (k (σ x) (σ x)) (σ y)) = (k (k (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13419 eq17723
    | exact resolve eq17723 eq13419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13419 eq17723
  have eq20018 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq6911
    | (have j0 := eq6911 (σ x)
       grind)
    | exact resolve eq6911 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6911
  have eq20263 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq9753 eq20018
    | (have r₁ := eq20018
       have r₂ := eq9753
       grind)
    | exact resolve eq20018 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20018
  have eq20267 : (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (k x x) := by grind
  clear eq20263
  have eq20268 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq9772 eq20267
    | exact resolve eq20267 eq9772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9772 eq20267
  have eq20278 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20268 eq17394
    | exact resolve eq17394 eq20268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17394
  have eq20279 : (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20268 eq17567
    | exact resolve eq17567 eq20268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17567 eq20268
  have eq20289 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq12732 eq20278
    | exact resolve eq20278 eq12732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20278
  have eq20521 : (M.op (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20279 eq9775
    | exact resolve eq9775 eq20279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9775 eq20279
  have eq20537 : (M.op (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by grind
  clear eq20521
  have eq20544 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20289 eq20537
    | exact resolve eq20537 eq20289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20289 eq20537
  have eq20743 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20544 eq6113
    | (have j0 := eq6113 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq6113 eq20544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq20744 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq9753 eq20743
    | exact resolve eq20743 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20743
  have eq20751 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq20744
       have r₂ := eq27
       grind)
    | exact resolve eq20744 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20744
  have eq20756 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ x))) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20751 eq132
    | exact resolve eq132 eq20751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq20751
  have eq20774 : (k (M.op x y) x) = (k (M.op x y) y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq131 eq20756
    | exact resolve eq20756 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq20756
  have eq20778 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq12632 eq20774
    | exact resolve eq20774 eq12632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12632 eq20774
  have eq29373 : (M.op x y) ≠ (k x x) ∨ (k (M.op x y) x) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6655 eq192
    | (have j0 := eq192 x y
       grind)
    | exact resolve eq192 eq6655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29382 : (k (σ (M.op x y)) (σ y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ x) (σ x)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20544 eq192
    | (have j0 := eq192 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq192 x y
       have r₂ := eq20544
       grind)
    | exact resolve eq192 eq20544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq20544
  have eq29429 : (k (σ x) (σ x)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq29382
       have r₂ := eq12732
       grind)
    | exact resolve eq29382 eq12732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29382
  have eq29433 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq29373
       have r₂ := eq20778
       grind)
    | exact resolve eq29373 eq20778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20778 eq29373
  have eq29527 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq9753 eq29429
    | exact resolve eq29429 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9753 eq29429
  have eq29606 : (k (σ (M.op x y)) (σ x)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq29433 eq37
    | exact resolve eq37 eq29433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq29433
  have eq29609 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq29606
    | exact resolve eq29606 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq29606
  have eq29611 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq29609
    | exact resolve eq29609 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29609
  have eq29612 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12732 eq29611
    | exact resolve eq29611 eq12732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12732 eq29611
  have eq29613 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq29612
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29612
    | exact resolve eq29612 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29612
  have eq29699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq29527 eq7490
    | exact resolve eq7490 eq29527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7490 eq29527
  have eq29710 : (M.op x y) = (k x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq29699
       have r₂ := eq27
       grind)
    | exact resolve eq29699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29699
  have eq29739 : ∀ X0 : G, (M.op X0 (k (M.op x y) (M.op x y))) = (M.op X0 x) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq727 x x
       have i₂ := eq29710
       grind)
    | exact superpose eq29710 eq727
    | exact resolve eq727 eq29710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq29710
  have eq29746 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq218 eq29739
    | exact resolve eq29739 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq29739
  have eq29764 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq29746 X0
       have i₂ := eq6551 X0
       grind)
    | exact superpose eq6551 eq29746
    | exact resolve eq29746 eq6551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6551 eq29746
  have eq30389 : (k x y) = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29764 y
       have i₂ := eq7501
       grind)
    | exact superpose eq7501 eq29764
    | exact resolve eq29764 eq7501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7501 eq29764
  have eq30519 : x = (k x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq6671 eq30389
    | exact resolve eq30389 eq6671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30389
  have eq30531 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq30519
       have r₂ := eq8441
       grind)
    | exact resolve eq30519 eq8441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8441 eq30519
  have eq30561 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq30531 eq6689
    | exact resolve eq6689 eq30531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6689 eq30531
  have eq33265 : x ≠ (M.op y (M.op x y)) ∨ x = (M.op y x) := by grind
  clear eq30561
  have eq33267 : x = (M.op y x) := by
    first
    | (have r₁ := eq33265
       have r₂ := eq6671
       grind)
    | exact resolve eq33265 eq6671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6671 eq33265
  have eq33320 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (k x x)) := by
    intro X0
    first
    | (have i₁ := eq665 y x x
       have i₂ := eq33267
       grind)
    | exact superpose eq33267 eq665
    | exact resolve eq665 eq33267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq33267
  have eq33331 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq33320 X0
       have i₂ := eq6700 X0
       grind)
    | exact superpose eq6700 eq33320
    | exact resolve eq33320 eq6700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6700 eq33320
  have eq33356 : (k x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq33331 x
       grind)
    | exact superpose eq33331 eq182
    | exact resolve eq182 eq33331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33331
  have eq33478 : (M.op x y) = (k x x) := by
    first
    | exact superpose eq6655 eq33356
    | exact resolve eq33356 eq6655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655 eq33356
  have eq33515 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq33478
       grind)
    | exact superpose eq33478 eq39
    | exact resolve eq39 eq33478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq33478
  have eq33532 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq33515
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33515
    | exact resolve eq33515 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq33515
  have eq33547 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq33532
    | exact resolve eq33532 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq33532
  have eq33568 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33547 eq7631
    | exact resolve eq7631 eq33547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7631
  have eq33582 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq33547 eq17724
    | exact resolve eq17724 eq33547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17724
  have eq33585 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33547 eq17740
    | exact resolve eq17740 eq33547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17740
  have eq33613 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29613 eq33585
    | exact resolve eq33585 eq29613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29613 eq33585
  have eq33622 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq33568
       have r₂ := eq27
       grind)
    | exact resolve eq33568 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33568
  have eq35805 : (k (k (σ (M.op x y)) (M.op (σ x) (σ y))) (k (σ (M.op x y)) (M.op (σ x) (σ y)))) = (M.op (k (σ (M.op x y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq33582 eq182
    | exact resolve eq182 eq33582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33582
  have eq35926 : (k (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) = (M.op (k (σ (M.op x y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq33613 eq35805
    | exact resolve eq35805 eq33613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33613 eq35805
  have eq35943 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq33622 eq35926
    | exact resolve eq35926 eq33622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33622 eq35926
  have eq35957 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq6854 eq35943
    | exact resolve eq35943 eq6854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6854 eq35943
  have eq36008 : (k (M.op (σ x) (σ y)) (σ y)) ≠ (k (M.op (σ x) (σ y)) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq35957 eq17381
    | (have j0 := eq17381 (σ x)
       grind)
    | (have r₁ := eq17381 (σ x)
       have r₂ := eq35957
       grind)
    | exact resolve eq17381 eq35957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17381 eq35957
  have eq36030 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq36008
  have eq36036 : (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33547 eq36030
    | exact resolve eq36030 eq33547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36030
  have eq36046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq36036 eq9086
    | exact resolve eq9086 eq36036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9086 eq36036
  have eq36054 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have r₁ := eq36046
       have r₂ := eq27
       grind)
    | exact resolve eq36046 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36046
  have eq36059 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq36054 eq6915
    | exact resolve eq6915 eq36054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6915 eq36054
  have eq36608 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq36059 eq26
    | (have j1 := eq36059 (σ x)
       grind)
    | exact resolve eq26 eq36059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq36059
  have eq36641 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36608
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq36608
    | exact resolve eq36608 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq36608
  have eq36680 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33547 eq36641
    | exact resolve eq36641 eq33547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33547 eq36641
  have eq36701 : False := by grind
  exact eq36701

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pxx_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
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
  have eq124 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  have eq163 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq85
    | exact resolve eq85 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq174 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 X1 X2 X3
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X1) X1) X1
       have r₂ := eq16 X1 X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 X1 X2
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq181
    | (have j0 := eq181 X0 X1 X2
       grind)
    | exact resolve eq181 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq186 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X1 X2
       have i₂ := eq178 X0 X1 (M.op (M.op X2 X1) X0) X2
       grind)
    | exact superpose eq178 eq183
    | (have j0 := eq183 X0 X1 X2
       grind)
    | exact resolve eq183 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq189 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X1 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq182 X1
       grind)
    | exact superpose eq182 eq190
    | (have j0 := eq190 X0 X1
       grind)
    | (have r₁ := eq190 X0 X0
       have r₂ := eq182 X0
       grind)
    | exact resolve eq190 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq195 : (M.op (M.op x y) y) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq174 sF0
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq174
    | exact resolve eq174 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (k (M.op (M.op x y) X0) X0) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq174 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) y) y
       have r₂ := eq174 y
       grind)
    | exact resolve eq13 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq199 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 X1
       have i₂ := eq16 X1 y X0
       grind)
    | exact superpose eq16 eq197
    | exact resolve eq197 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq200 : ∀ X0 : G, (M.op X0 y) ≠ (k X0 X0) ∨ (k (M.op (M.op x y) X0) X0) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq196 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq196
    | (have j0 := eq196 X0
       grind)
    | exact resolve eq196 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq202 : ∀ X0 : G, (M.op X0 y) ≠ (k X0 X0) ∨ (k (M.op (M.op x y) X0) X0) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq199 eq200
    | (have j0 := eq200 X0
       grind)
    | exact resolve eq200 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq200
  have eq206 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq175 sF4
       have i₂ := eq182 sF4
       grind)
    | exact superpose eq182 eq175
    | exact resolve eq175 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq211 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq208 x X0
       have i₂ := eq16 X0 sF3 x
       grind)
    | exact superpose eq16 eq208
    | exact resolve eq208 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq217 : ∀ X0 : G, (M.op X0 (k (M.op x y) (M.op x y))) = (M.op X0 (M.op (M.op (M.op x y) y) X0)) := by
    intro X0
    first
    | exact superpose eq195 eq16
    | exact resolve eq16 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq218 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq217 X0
       have i₂ := eq16 X0 y sF0
       grind)
    | exact superpose eq16 eq217
    | exact resolve eq217 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq241 : ∀ X0 : G, (M.op X0 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq206 eq16
    | exact resolve eq16 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq242 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq241 X0
       have i₂ := eq16 X0 sF3 sF4
       grind)
    | exact superpose eq16 eq241
    | exact resolve eq241 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq371 : (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq242 eq182
    | exact resolve eq182 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ y)) (σ X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | exact superpose eq132 eq34
    | exact resolve eq34 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq455 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ x))) = (σ (k X0 (k x x))) := by
    intro X0
    first
    | exact superpose eq97 eq38
    | exact resolve eq38 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op (k X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X2 X0 X1 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq178
    | exact resolve eq178 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 (M.op X0 X1) X1 X2 X0
       have i₂ := eq182 (M.op X0 X1)
       grind)
    | exact superpose eq182 eq178
    | exact resolve eq178 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 (M.op (M.op X0 X1) X2)
       have i₂ := eq178 X2 X1 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq178 eq182
    | exact resolve eq182 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X3) X0) = (M.op (M.op (M.op X2 X1) X3) (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X3) X0
       have i₂ := eq178 X3 X1 X0 X2
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq178 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq13 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq178 X0 X1 X1 X3
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k (M.op (M.op X2 X1) X3) X0) = (M.op (M.op (M.op X2 X1) X3) (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq671 X0 X1 X2 X3
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq671
    | (have j0 := eq671 X0 X1 X2 X3
       grind)
    | exact resolve eq671 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq691 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k (M.op (M.op X2 X1) X3) X0) = (M.op (M.op (M.op X2 X1) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq679 X0 X1 X2 X3
       have i₂ := eq178 X3 X1 (M.op (M.op X2 X1) X3) X2
       grind)
    | exact superpose eq178 eq679
    | (have j0 := eq679 X0 X1 X2 X3
       grind)
    | exact resolve eq679 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq692 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq189
    | exact resolve eq189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq717 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (k X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq652 (σ X0) X1 X2
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq652
    | exact resolve eq652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1 (k X0 X0)
       have i₂ := eq182 (k X0 X0)
       grind)
    | exact superpose eq182 eq652
    | exact resolve eq652 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq869 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq928 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq901 X0 X1 X2
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq901
    | (have j0 := eq901 X0 X1 X2
       grind)
    | exact resolve eq901 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq949 : ∀ X0 X1 : G, (k X1 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq919 X0 X1
       have i₂ := eq182 X1
       grind)
    | exact superpose eq182 eq919
    | (have j0 := eq919 X0 X1
       grind)
    | exact resolve eq919 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq981 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq928 X0 X1 X2
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq928
    | (have j0 := eq928 X0 X1 X2
       grind)
    | exact resolve eq928 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1000 : ∀ X0 X1 : G, (k X1 X0) = (k X1 X1) ∨ (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq949 X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq949
    | (have j0 := eq949 X0 X1
       grind)
    | exact resolve eq949 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq1031 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1032 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1031 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq1031
    | (have j0 := eq1031 X0
       grind)
    | exact resolve eq1031 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1034 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1032 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq1032
    | (have j0 := eq1032 X0
       grind)
    | exact resolve eq1032 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq6985 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq981 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq6986 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6985 X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq6985
    | (have j0 := eq6985 X0 X1
       grind)
    | (have r₁ := eq6985 X0 X0
       have r₂ := eq182 X0
       grind)
    | exact resolve eq6985 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6985
  have eq7037 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6986 X0 X1
       have j1 := eq1000 X1 X0
       grind)
    | (have r₁ := eq6986 X1 X0
       have r₂ := eq1000 X0 X1
       grind)
    | (have r₁ := eq6986 X0 X0
       have r₂ := eq1000 X0 X0
       grind)
    | (have r₁ := eq6986 X0 X0
       have r₂ := eq1000 X0 (k X0 X0)
       grind)
    | exact resolve eq6986 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6986
  have eq7133 : (M.op x y) = (k x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7037 x y
       grind)
    | exact superpose eq7037 eq18
    | (have j1 := eq7037 x y
       grind)
    | exact resolve eq18 eq7037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7139 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq7037 sF2 sF3
       grind)
    | exact superpose eq7037 eq26
    | (have j1 := eq7037 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq7037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7190 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq7133
       grind)
    | exact superpose eq7133 eq40
    | exact resolve eq40 eq7133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7133
  have eq7191 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq7190
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7190
    | exact resolve eq7190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7190
  have eq7195 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq20 eq7191
    | exact resolve eq7191 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7191
  have eq7203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq7195 eq7139
    | exact resolve eq7139 eq7195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7139 eq7195
  have eq7210 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have r₁ := eq7203
       have r₂ := eq27
       grind)
    | exact resolve eq7203 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7203
  have eq7214 : (τ (σ x)) = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq7210 eq115
    | exact resolve eq115 eq7210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq7210
  have eq7226 : x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq7214
    | exact resolve eq7214 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7214
  have eq7227 : x = (k y y) := by grind
  clear eq7226
  have eq7235 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq7227
       grind)
    | exact superpose eq7227 eq40
    | exact resolve eq40 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7237 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (k x x)) := by
    intro X0
    first
    | (have i₁ := eq727 y x
       have i₂ := eq7227
       grind)
    | exact superpose eq7227 eq727
    | exact resolve eq727 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7238 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq717 y X0 X1
       have i₂ := eq7227
       grind)
    | exact superpose eq7227 eq717
    | exact resolve eq717 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7239 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq692 y X0
       have i₂ := eq7227
       grind)
    | exact superpose eq7227 eq692
    | exact resolve eq692 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq7240 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq652 y X0 X1
       have i₂ := eq7227
       grind)
    | exact superpose eq7227 eq652
    | exact resolve eq652 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7242 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq7239 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7239
    | (have j0 := eq7239 X0
       grind)
    | exact resolve eq7239 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7239
  have eq7243 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7238 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7238
    | (have j0 := eq7238 X0 X1
       grind)
    | exact resolve eq7238 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7238
  have eq7244 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7235
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7235
    | exact resolve eq7235 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7235
  have eq7248 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq7242 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7242
    | (have j0 := eq7242 X0
       grind)
    | exact resolve eq7242 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7242
  have eq7249 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7243 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7243
    | (have j0 := eq7243 X0 X1
       grind)
    | exact resolve eq7243 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7243
  have eq7250 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7244
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7244
    | exact resolve eq7244 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7244
  have eq7255 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq7250 eq1034
    | exact resolve eq1034 eq7250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq7256 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq7250 eq727
    | exact resolve eq727 eq7250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq7274 : (k (k x x) (k x x)) = (M.op (k x x) y) := by
    first
    | (have i₁ := eq182 (k x x)
       have i₂ := eq7237 (k x x)
       grind)
    | exact superpose eq7237 eq182
    | exact resolve eq182 eq7237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7237
  have eq7310 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7240 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7240
    | (have j0 := eq7240 X0 y
       grind)
    | exact resolve eq7240 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7341 : ∀ X0 : G, (M.op (M.op x X0) y) = (k (M.op x X0) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq182 (M.op x X0)
       have i₂ := eq7240 (M.op x X0) X0
       grind)
    | exact superpose eq7240 eq182
    | exact resolve eq182 eq7240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7344 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (k (M.op x X1) X0) = (M.op (M.op x X1) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op x X1) X0
       have i₂ := eq7240 X0 X1
       grind)
    | exact superpose eq7240 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y (M.op x X1)
       have r₂ := eq7240 (M.op x X1) X1
       grind)
    | (have r₁ := eq13 (M.op x X1) y
       have r₂ := eq7240 y X1
       grind)
    | exact resolve eq13 eq7240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7351 : ∀ X0 X1 : G, (k (M.op x X1) (M.op x X1)) = X0 ∨ (M.op X0 y) = (k X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7037 X0 (M.op x X1)
       have i₂ := eq7240 X0 X1
       grind)
    | exact superpose eq7240 eq7037
    | (have j0 := eq7037 X0 (M.op x X1)
       grind)
    | exact resolve eq7037 eq7240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7367 : ∀ X0 X1 : G, (M.op X0 y) ≠ (k X0 X0) ∨ (k (M.op x X1) X0) = (M.op (M.op x X1) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7344 X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq7344
    | (have j0 := eq7344 X0 X1
       grind)
    | exact resolve eq7344 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7344
  have eq7373 : ∀ X0 X1 : G, (k X0 X0) ≠ (M.op X0 (M.op x y)) ∨ (k (M.op x X1) X0) = (M.op (M.op x X1) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7367 X0 X1
       have i₂ := eq7310 X0
       grind)
    | exact superpose eq7310 eq7367
    | (have j0 := eq7367 X0 X1
       grind)
    | exact resolve eq7367 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7367
  have eq7379 : ∀ X0 X1 : G, (k (M.op x X1) X0) = (M.op (M.op x X1) y) ∨ (k X0 X0) ≠ (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq7373 X0 X1
       have i₂ := eq7240 (M.op x X1) X1
       grind)
    | exact superpose eq7240 eq7373
    | (have j0 := eq7373 X0 X1
       grind)
    | exact resolve eq7373 eq7240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7373
  have eq7384 : ∀ X0 X1 : G, (k X0 X0) ≠ (M.op X0 (M.op x y)) ∨ (k (M.op x X1) X0) = (M.op (M.op x X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq7379 X0 X1
       have i₂ := eq7310 (M.op x X1)
       grind)
    | exact superpose eq7310 eq7379
    | (have j0 := eq7379 X0 X1
       grind)
    | exact resolve eq7379 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7379
  have eq7397 : (k y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq7310 y
       grind)
    | exact superpose eq7310 eq182
    | exact resolve eq182 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7398 : ∀ X0 : G, (M.op y X0) ≠ (M.op y (M.op x y)) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq7310 y
       grind)
    | exact superpose eq7310 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq7310 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq7310 y
       grind)
    | exact resolve eq13 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7400 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op x y)) ∨ (k y X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq7310 X0
       grind)
    | exact superpose eq7310 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq7310 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq7310 y
       grind)
    | exact resolve eq13 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7414 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7310 x
       grind)
    | exact superpose eq7310 eq18
    | (have j1 := eq7310 x
       grind)
    | exact resolve eq18 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7427 : ∀ X0 : G, (k X0 X0) ≠ (M.op X0 (M.op x y)) ∨ (k y X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq7400 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq7400
    | (have j0 := eq7400 X0
       grind)
    | exact resolve eq7400 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7400
  have eq7429 : ∀ X0 : G, (M.op y X0) ≠ (M.op y (M.op x y)) ∨ (k X0 y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7398 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq7398
    | (have j0 := eq7398 X0
       grind)
    | exact resolve eq7398 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7398
  have eq7430 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq7397
       have i₂ := eq7227
       grind)
    | exact superpose eq7227 eq7397
    | exact resolve eq7397 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7397
  have eq7436 : ∀ X0 : G, (k y X0) = (k y y) ∨ (k X0 X0) ≠ (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7427 X0
       have i₂ := eq182 y
       grind)
    | exact superpose eq182 eq7427
    | (have j0 := eq7427 X0
       grind)
    | (have r₁ := eq7427 (M.op x y)
       have r₂ := eq182 (M.op x y)
       grind)
    | exact resolve eq7427 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427
  have eq7440 : ∀ X0 : G, (k X0 X0) ≠ (M.op X0 (M.op x y)) ∨ x = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq7436 X0
       have i₂ := eq7227
       grind)
    | exact superpose eq7227 eq7436
    | (have j0 := eq7436 X0
       grind)
    | exact resolve eq7436 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7436
  have eq7447 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq7414 eq178
    | exact resolve eq178 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7448 : ∀ X0 : G, (M.op X0 (k (M.op x y) (M.op x y))) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7414 eq665
    | exact resolve eq665 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7452 : (M.op x y) = (k x (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7414 eq7037
    | (have j0 := eq7037 x (M.op x y)
       grind)
    | exact resolve eq7037 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7458 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq7430 eq178
    | exact resolve eq178 eq7430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq7529 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq7248
    | (have j0 := eq7248 (σ y)
       grind)
    | exact resolve eq7248 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7248
  have eq7588 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7529
       have i₂ := eq182 sF3
       grind)
    | exact superpose eq182 eq7529
    | exact resolve eq7529 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7529
  have eq7592 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7250 eq7588
    | exact resolve eq7588 eq7250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7588
  have eq7598 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq7592 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq13 eq7592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7601 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq7592 eq665
    | exact resolve eq665 eq7592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7592
  have eq7606 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq7256 eq7601
    | exact resolve eq7601 eq7256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7601
  have eq7609 : (σ x) ≠ (k (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq7598
       have i₂ := eq182 sF3
       grind)
    | exact superpose eq182 eq7598
    | exact resolve eq7598 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7598
  have eq7612 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have r₁ := eq7609
       have r₂ := eq7250
       grind)
    | exact resolve eq7609 eq7250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7609
  have eq7613 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq7612
       have i₂ := eq182 sF4
       grind)
    | exact superpose eq182 eq7612
    | exact resolve eq7612 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7612
  have eq7623 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7606 eq182
    | exact resolve eq182 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7624 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq7606 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq7606 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq7606 (σ y)
       grind)
    | exact resolve eq13 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7626 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq7606 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq7606 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq7606 (σ y)
       grind)
    | exact resolve eq13 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7656 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (k X0 X0) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq7626 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq7626
    | (have j0 := eq7626 X0
       grind)
    | exact resolve eq7626 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7626
  have eq7658 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7624 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq7624
    | (have j0 := eq7624 X0
       grind)
    | exact resolve eq7624 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7624
  have eq7659 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq7613 eq7623
    | exact resolve eq7623 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7623
  have eq7666 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X0) ∨ (M.op X0 (σ y)) ≠ (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7656 X0
       have i₂ := eq182 sF4
       grind)
    | exact superpose eq182 eq7656
    | (have j0 := eq7656 X0
       grind)
    | (have r₁ := eq7656 (σ y)
       have r₂ := eq182 (σ y)
       grind)
    | exact resolve eq7656 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7656
  have eq7670 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (k X0 X0) ∨ (k (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq7613 eq7666
    | (have j0 := eq7666 X0
       grind)
    | exact resolve eq7666 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7666
  have eq7672 : (M.op (k (M.op (σ x) (σ y)) (σ y)) (σ y)) = (k (k (M.op (σ x) (σ y)) (σ y)) (k (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq7613 eq371
    | exact resolve eq371 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq7673 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq7613 eq242
    | exact resolve eq242 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq7679 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (k (M.op (σ x) (σ y)) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7613 eq652
    | exact resolve eq652 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq7613
  have eq7682 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (k (M.op (σ x) (σ y)) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7606 eq7679
    | exact resolve eq7679 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7606 eq7679
  have eq7702 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (k (σ x) X0)) ∨ (σ x) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7249 X0 X1
       have i₂ := eq7037 sF2 X1
       grind)
    | exact superpose eq7037 eq7249
    | (have j1 := eq7037 (σ x) X0
       grind)
    | exact resolve eq7249 eq7037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7782 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq7256 eq182
    | exact resolve eq182 eq7256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7864 : ∀ X0 : G, (k (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7447 eq182
    | exact resolve eq182 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7923 : (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq7448 eq182
    | exact resolve eq182 eq7448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8014 : ∀ X0 : G, (k (M.op x X0) (M.op x X0)) = (M.op (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 (M.op x X0)
       have i₂ := eq7458 (M.op x X0) X0
       grind)
    | (have i₁ := eq182 (M.op x y)
       have i₂ := eq7458 (M.op x y) x
       grind)
    | exact superpose eq7458 eq182
    | exact resolve eq182 eq7458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8024 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (k X0 (M.op x X1)) ∨ (k (M.op x X1) (M.op x X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7037 X0 (M.op x X1)
       have i₂ := eq7458 X0 X1
       grind)
    | (have i₁ := eq7037 X0 (M.op x y)
       have i₂ := eq7458 X0 X1
       grind)
    | exact superpose eq7458 eq7037
    | (have j0 := eq7037 X0 (M.op x X1)
       grind)
    | exact resolve eq7037 eq7458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8042 : ∀ X0 X1 : G, (M.op (M.op x X1) y) = X0 ∨ (M.op X0 (M.op x y)) = (k X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8024 X0 X1
       have i₂ := eq7341 X1
       grind)
    | exact superpose eq7341 eq8024
    | (have j0 := eq8024 X0 X1
       grind)
    | exact resolve eq8024 eq7341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8024
  have eq8053 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (k X0 (M.op x X1)) ∨ (M.op (M.op x X1) (M.op x y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8042 X0 X1
       have i₂ := eq7310 (M.op x X1)
       grind)
    | exact superpose eq7310 eq8042
    | (have j0 := eq8042 X0 X1
       grind)
    | exact resolve eq8042 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8042
  have eq8309 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k (M.op (M.op X1 X0) X0) X0) = (M.op (M.op (M.op X1 X0) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq186
    | (have j0 := eq186 X0 X0 X1
       grind)
    | (have r₁ := eq186 X0 X0 x
       have r₂ := eq182 X0
       grind)
    | exact resolve eq186 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8344 : ∀ X0 : G, x ≠ (k y y) ∨ (k (M.op (M.op X0 (M.op x y)) y) y) = (M.op (M.op (M.op X0 (M.op x y)) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7430 eq186
    | (have j0 := eq186 y (M.op x y) X0
       grind)
    | exact resolve eq186 eq7430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq8358 : ∀ X0 X1 : G, (k (M.op (M.op X1 X0) X0) X0) = (M.op (M.op (M.op X1 X0) X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq8309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8309
  have eq8368 : ∀ X0 : G, (k (M.op (M.op X0 (M.op x y)) y) y) = (M.op (M.op (M.op X0 (M.op x y)) y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq8344 X0
       grind)
    | (have r₁ := eq8344 X0
       have r₂ := eq7227
       grind)
    | exact resolve eq8344 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8344
  have eq8406 : ∀ X0 : G, (k (M.op (M.op X0 (M.op x y)) (M.op x y)) y) = (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq8368 X0
       have i₂ := eq7310 (M.op X0 sF0)
       grind)
    | exact superpose eq7310 eq8368
    | exact resolve eq8368 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8368
  have eq8444 : ∀ X0 : G, (k (M.op (M.op X0 (M.op x y)) (M.op x y)) y) = (k (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq8406 x
       have i₂ := eq8358 sF0 x
       grind)
    | exact superpose eq8358 eq8406
    | exact resolve eq8406 eq8358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8406
  have eq8558 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq7255 eq152
    | exact resolve eq152 eq7255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq7255
  have eq8560 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq8558
    | exact resolve eq8558 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8558
  have eq8656 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (σ x) (σ x))) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq8560 eq665
    | exact resolve eq665 eq8560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8662 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq7256 eq8656
    | exact resolve eq8656 eq7256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8656
  have eq8670 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7452 eq35
    | exact resolve eq35 eq7452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8673 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq8670
    | exact resolve eq8670 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8670
  have eq9282 : (M.op x y) ≠ (k x x) ∨ x = (k y x) := by
    first
    | exact superpose eq7414 eq7440
    | (have j0 := eq7440 x
       grind)
    | exact resolve eq7440 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7440
  have eq10383 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq8662 eq26
    | (have j1 := eq8662 (σ x)
       grind)
    | exact resolve eq26 eq8662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10386 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq8662 eq7659
    | exact resolve eq7659 eq8662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8662
  have eq10390 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10383
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq10383
    | exact resolve eq10383 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10383
  have eq10419 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (k x y) := by
    first
    | exact superpose eq10390 eq97
    | exact resolve eq97 eq10390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11103 : (k (σ (k x x)) (k (σ x) (σ x))) = (σ (M.op (k x x) y)) := by
    first
    | (have i₁ := eq455 (k x x)
       have i₂ := eq7274
       grind)
    | exact superpose eq7274 eq455
    | exact resolve eq455 eq7274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq7274
  have eq11121 : (k (σ (k x x)) (k (σ x) (σ x))) = (σ (M.op (k x x) (M.op x y))) := by
    first
    | (have i₁ := eq11103
       have i₂ := eq7310 (k x x)
       grind)
    | exact superpose eq7310 eq11103
    | exact resolve eq11103 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11103
  have eq11129 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (k x x) (M.op x y))) := by
    first
    | (have i₁ := eq11121
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq11121
    | exact resolve eq11121 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11121
  have eq11137 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (k x x) (M.op x y))) := by
    first
    | (have i₁ := eq11129
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11129
    | exact resolve eq11129 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11129
  have eq11143 : (M.op (k (σ x) (σ x)) (σ y)) = (σ (M.op (k x x) (M.op x y))) := by
    first
    | exact superpose eq7782 eq11137
    | exact resolve eq11137 eq7782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7782 eq11137
  have eq11221 : (M.op (k x x) (M.op x y)) = (τ (M.op (k (σ x) (σ x)) (σ y))) := by
    first
    | exact superpose eq11143 eq15
    | exact resolve eq15 eq11143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11143
  have eq11440 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op x X0))) = (M.op X1 (M.op (σ (M.op (M.op x X0) y)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq717 (M.op x X0) X1 X2
       have i₂ := eq7341 X0
       grind)
    | exact superpose eq7341 eq717
    | exact resolve eq717 eq7341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq11448 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op x X0))) = (M.op X1 (M.op (σ (M.op (M.op x X0) (M.op x y))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11440 X0 X1 X2
       have i₂ := eq7310 (M.op x X0)
       grind)
    | exact superpose eq7310 eq11440
    | exact resolve eq11440 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11440
  have eq13276 : ∀ X0 : G, (k y X0) ≠ (M.op y (M.op x y)) ∨ (k X0 y) = (k X0 X0) ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7429 X0
       have i₂ := eq7037 y X0
       grind)
    | exact superpose eq7037 eq7429
    | (have j0 := eq7429 X0
       have j1 := eq7037 (k X0 y) X0
       grind)
    | exact resolve eq7429 eq7037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13294 : ∀ X0 : G, (M.op y (M.op x y)) ≠ (M.op y (M.op x y)) ∨ (k (M.op x X0) (M.op x X0)) = (k (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq7429 (M.op x X0)
       have i₂ := eq7458 y X0
       grind)
    | (have i₁ := eq7429 (M.op x y)
       have i₂ := eq7458 y x
       grind)
    | exact superpose eq7458 eq7429
    | (have j0 := eq7429 (M.op x y)
       grind)
    | (have r₁ := eq7429 (M.op x y)
       have r₂ := eq7458 y y
       grind)
    | (have r₁ := eq7429 (M.op x x)
       have r₂ := eq7458 y x
       grind)
    | exact resolve eq7429 eq7458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7458
  have eq13296 : ∀ X0 : G, (M.op y (M.op x y)) ≠ (M.op y (M.op x y)) ∨ (k (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (k (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq7447 eq7429
    | (have j0 := eq7429 (M.op x y)
       grind)
    | (have r₁ := eq7429 (M.op (M.op x y) x)
       have r₂ := eq7447 y x
       grind)
    | exact resolve eq7429 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7447
  have eq13313 : (M.op y (M.op x y)) ≠ (M.op y (M.op x y)) ∨ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (k (k (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq7448 eq7429
    | (have j0 := eq7429 (M.op x y)
       grind)
    | (have r₁ := eq7429 (k (M.op x y) (M.op x y))
       have r₂ := eq7448 y
       grind)
    | exact resolve eq7429 eq7448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13338 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq7429 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13343 : (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (k (k (M.op x y) (M.op x y)) y) := by grind
  clear eq13313
  have eq13347 : ∀ X0 : G, (k (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (k (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have j0 := eq13296 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13296
  have eq13348 : ∀ X0 : G, (k (M.op x X0) (M.op x X0)) = (k (M.op x X0) y) := by
    intro X0
    first
    | (have j0 := eq13294 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13294
  have eq13389 : ∀ X0 : G, x ≠ (k y X0) ∨ (k X0 y) = (k X0 X0) ∨ y = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq7430 eq13276
    | (have j0 := eq13276 X0
       grind)
    | exact resolve eq13276 eq7430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13276
  have eq13426 : ∀ X0 : G, (σ (k (k (M.op x y) (M.op x y)) X0)) = (k (k (σ (M.op x y)) (σ y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq13338 eq396
    | exact resolve eq396 eq13338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq13429 : (k (σ (M.op x y)) (σ y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq13338 eq40
    | exact resolve eq40 eq13338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13430 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq13429
    | exact resolve eq13429 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13429
  have eq13432 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq13430
    | exact resolve eq13430 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13430
  have eq13724 : (M.op (k (M.op x y) (M.op x y)) (M.op x y)) = (k (k (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq13343 eq7923
    | exact resolve eq7923 eq13343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7923 eq13343
  have eq14472 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (k (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq13347 eq7864
    | exact resolve eq7864 eq13347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7864 eq13347
  have eq14860 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (k (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq8014 X0
       have i₂ := eq13348 X0
       grind)
    | exact superpose eq13348 eq8014
    | exact resolve eq8014 eq13348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8014 eq13348
  have eq17865 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) = (k (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq211 eq7658
    | (have j0 := eq7658 (σ y)
       grind)
    | (have r₁ := eq7658 (M.op (M.op (σ x) (σ y)) X0)
       have r₂ := eq211 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq7658 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq17897 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k (k (M.op (σ x) (σ y)) (σ y)) (k (M.op (σ x) (σ y)) (σ y))) = (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7673 eq7658
    | (have j0 := eq7658 (σ y)
       grind)
    | (have r₁ := eq7658 (k (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq7673 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq7658 eq7673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7673
  have eq17906 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (k (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq7659 eq7658
    | (have j0 := eq7658 X0
       grind)
    | exact resolve eq7658 eq7659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17919 : (k (k (M.op (σ x) (σ y)) (σ y)) (k (M.op (σ x) (σ y)) (σ y))) = (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq17897
  have eq17926 : ∀ X0 : G, (k (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) = (k (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq17865 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17865
  have eq18308 : (M.op (k (M.op (σ x) (σ y)) (σ y)) (σ y)) = (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17919 eq7672
    | exact resolve eq7672 eq17919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7672 eq17919
  have eq18330 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq18308 eq7682
    | exact resolve eq7682 eq18308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7682 eq18308
  have eq18701 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq17926 eq665
    | exact resolve eq665 eq17926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17926
  have eq18835 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (k (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18701 X1 X1
       have i₂ := eq7037 sF4 X1
       grind)
    | exact superpose eq7037 eq18701
    | (have j1 := eq7037 (M.op (σ x) (σ y)) X0
       grind)
    | exact resolve eq18701 eq7037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18701
  have eq20723 : ∀ X0 : G, (σ (k X0 X0)) ≠ (M.op (σ X0) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7670 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq7670
    | (have j0 := eq7670 (σ X0)
       grind)
    | exact resolve eq7670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7670
  have eq22860 : (k (M.op (σ x) (σ y)) (σ y)) ≠ (k (M.op (σ x) (σ y)) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (k x y) := by
    first
    | exact superpose eq10386 eq17906
    | (have j0 := eq17906 (σ x)
       grind)
    | (have r₁ := eq17906 (σ x)
       have r₂ := eq10386
       grind)
    | exact resolve eq17906 eq10386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10386 eq17906
  have eq22954 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (k x y) := by grind
  clear eq22860
  have eq23015 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (k x y) := by
    first
    | exact superpose eq10390 eq22954
    | exact resolve eq22954 eq10390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22954
  have eq25002 : (k (M.op (M.op x y) (M.op x y)) y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq7414 eq8444
    | exact resolve eq8444 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8444
  have eq25017 : (k (k (M.op x y) (M.op x y)) (M.op x y)) = (k (k (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq25002
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq25002
    | exact resolve eq25002 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25002
  have eq25035 : (k (σ (k (M.op x y) (M.op x y))) (σ y)) = (σ (k (k (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq25017 eq40
    | exact resolve eq40 eq25017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25036 : (k (σ (k (M.op x y) (M.op x y))) (σ y)) = (k (σ (k (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq25035
    | exact resolve eq25035 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25035
  have eq25039 : (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq25036
    | exact resolve eq25036 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25036
  have eq25042 : (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq25039
    | exact resolve eq25039 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25039
  have eq25045 : (k (k (σ (M.op x y)) (σ y)) (σ y)) = (k (k (σ (M.op x y)) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13432 eq25042
    | exact resolve eq25042 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25042
  have eq30439 : (σ x) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq8560 eq192
    | (have j0 := eq192 (σ y) (σ x)
       grind)
    | exact resolve eq192 eq8560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq8560
  have eq30481 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq30439
       have r₂ := eq7250
       grind)
    | exact resolve eq30439 eq7250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30439
  have eq30575 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq10390 eq30481
    | exact resolve eq30481 eq10390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30481
  have eq36282 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (k (σ x) (σ (M.op x X0))) ∨ x = (M.op (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq35 (M.op x X0)
       have i₂ := eq8053 x X0
       grind)
    | exact superpose eq8053 eq35
    | (have j1 := eq8053 x X0
       grind)
    | exact resolve eq35 eq8053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8053
  have eq36305 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op x X0))) ∨ x = (M.op (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7414 eq36282
    | (have j0 := eq36282 X0
       grind)
    | exact resolve eq36282 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36282
  have eq36339 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op x X0))) ∨ x = (M.op (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq36305
    | (have j0 := eq36305 X0
       grind)
    | exact resolve eq36305 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36305
  have eq36357 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op x X0))) ∨ x = (k (M.op x X0) y) := by
    intro X0
    first
    | exact superpose eq14860 eq36339
    | (have j0 := eq36339 X0
       grind)
    | exact resolve eq36339 eq14860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36339
  have eq36398 : (σ (M.op x y)) = (k (σ x) (σ (k x x))) ∨ x = (k (k x x) y) := by
    first
    | (have i₁ := eq36357 x
       have i₂ := eq182 x
       grind)
    | exact superpose eq182 eq36357
    | exact resolve eq36357 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36357
  have eq36565 : (σ (M.op x y)) = (k (σ x) (k (σ x) (σ x))) ∨ x = (k (k x x) y) := by
    first
    | (have i₁ := eq36398
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq36398
    | exact resolve eq36398 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36398
  have eq36576 : (σ (M.op x y)) = (k (σ x) (k (σ x) (σ x))) ∨ x = (k (k x x) y) := by
    first
    | (have i₁ := eq36565
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36565
    | exact resolve eq36565 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36565
  have eq36745 : (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (k (k x x) y) ∨ x = (k x y) := by
    first
    | exact superpose eq10390 eq36576
    | exact resolve eq36576 eq10390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10390 eq36576
  have eq36760 : (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (k (τ (M.op (σ x) (σ y))) y) ∨ x = (k x y) := by
    first
    | exact superpose eq10419 eq36745
    | exact resolve eq36745 eq10419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10419 eq36745
  have eq36766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k (τ (M.op (σ x) (σ y))) y) ∨ x = (k x y) := by
    first
    | exact superpose eq23015 eq36760
    | exact resolve eq36760 eq23015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23015 eq36760
  have eq36769 : x = (k (τ (M.op (σ x) (σ y))) y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq36766
       have r₂ := eq27
       grind)
    | exact resolve eq36766 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36766
  have eq36783 : (σ x) = (k (σ (τ (M.op (σ x) (σ y)))) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq36769 eq40
    | exact resolve eq40 eq36769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36769
  have eq36786 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq36783
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq36783
    | exact resolve eq36783 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36783
  have eq36794 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq36786
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36786
    | exact resolve eq36786 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36786
  have eq46260 : (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq7414 eq8358
    | exact resolve eq8358 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46623 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op (σ x) X1)) (M.op (σ x) X1)) (M.op (σ x) X1)) = (M.op (M.op (M.op X0 (M.op (σ x) X1)) (M.op (σ x) X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq7249 (M.op (M.op X1 (M.op sF2 X1)) (M.op sF2 X1)) X1
       have i₂ := eq8358 (M.op sF2 X1) X1
       grind)
    | exact superpose eq8358 eq7249
    | exact resolve eq7249 eq8358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46695 : ∀ X0 : G, (k (M.op (M.op X0 (k (M.op x y) (M.op x y))) (k (M.op x y) (M.op x y))) (k (M.op x y) (M.op x y))) = (M.op (M.op (M.op X0 (k (M.op x y) (M.op x y))) (k (M.op x y) (M.op x y))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7448 (M.op (M.op x (k sF0 sF0)) (k sF0 sF0))
       have i₂ := eq8358 (k sF0 sF0) x
       grind)
    | exact superpose eq8358 eq7448
    | exact resolve eq7448 eq8358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7448
  have eq46738 : ∀ X0 : G, (k (M.op (M.op X0 (k (M.op x y) (M.op x y))) y) (k (M.op x y) (M.op x y))) = (M.op (M.op (M.op X0 (k (M.op x y) (M.op x y))) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq218 eq46695
    | exact resolve eq46695 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46695
  have eq46805 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) (M.op (σ x) X1)) = (M.op (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq7249 eq46623
    | exact resolve eq46623 eq7249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46623
  have eq47085 : (k (k (M.op x y) (M.op x y)) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq46260
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq46260
    | exact resolve eq46260 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46260
  have eq47249 : ∀ X0 : G, (M.op (M.op (M.op X0 (k (M.op x y) (M.op x y))) (M.op x y)) (M.op x y)) = (k (M.op (M.op X0 (k (M.op x y) (M.op x y))) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq46738 X0
       have i₂ := eq7310 (M.op X0 (k sF0 sF0))
       grind)
    | exact superpose eq7310 eq46738
    | exact resolve eq46738 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46738
  have eq47316 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) = (k (M.op (M.op X0 (σ y)) (σ y)) (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7249 eq46805
    | exact resolve eq46805 eq7249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7249 eq46805
  have eq47744 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) (M.op x y)) = (k (M.op (M.op X0 y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq218 eq47249
    | exact resolve eq47249 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq47249
  have eq47811 : ∀ X0 X1 : G, (k (M.op (M.op X0 (σ y)) (σ y)) (σ y)) = (k (M.op (M.op X0 (σ y)) (σ y)) (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47316 X1 X1
       have i₂ := eq8358 sF3 X1
       grind)
    | exact superpose eq8358 eq47316
    | exact resolve eq47316 eq8358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47316
  have eq48216 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op x y)) = (k (M.op (M.op X0 (M.op x y)) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq47744 X0
       have i₂ := eq7310 X0
       grind)
    | exact superpose eq7310 eq47744
    | exact resolve eq47744 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47744
  have eq48356 : ∀ X0 : G, (k (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op x y)) = (k (M.op (M.op X0 (M.op x y)) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq48216 x
       have i₂ := eq8358 sF0 x
       grind)
    | exact superpose eq8358 eq48216
    | exact resolve eq48216 eq8358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8358 eq48216
  have eq51452 : ∀ X0 : G, (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq47811
    | (have j0 := eq47811 (σ x) X0
       grind)
    | exact resolve eq47811 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47811
  have eq51637 : ∀ X0 : G, (k (k (M.op (σ x) (σ y)) (σ y)) (σ y)) = (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq7659 eq51452
    | exact resolve eq51452 eq7659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7659 eq51452
  have eq51670 : ∀ X0 : G, (k (σ x) (σ y)) = (k (σ x) (M.op (σ x) X0)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq36794 eq51637
    | exact resolve eq51637 eq36794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36794 eq51637
  have eq51843 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) X0)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq30575 eq51670
    | exact resolve eq51670 eq30575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51670
  have eq51849 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (k (σ x) X0)) ∨ x = (k x y) ∨ (σ x) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq51843 x
       have i₂ := eq7037 sF2 x
       grind)
    | exact superpose eq7037 eq51843
    | (have j1 := eq7037 (σ x) X0
       grind)
    | exact resolve eq51843 eq7037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51843
  have eq52876 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x X0))) = (M.op X1 (k (σ (M.op (M.op x X0) (M.op x y))) (σ (M.op (M.op x X0) (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq11448 X0 X1 (σ (M.op (M.op x X0) sF0))
       have i₂ := eq182 (σ (M.op (M.op x X0) sF0))
       grind)
    | exact superpose eq182 eq11448
    | exact resolve eq11448 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11448
  have eq53230 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x X0))) = (M.op X1 (σ (k (M.op (M.op x X0) (M.op x y)) (M.op (M.op x X0) (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq52876 X0 X1
       have i₂ := eq10 (M.op (M.op x X0) sF0) (M.op (M.op x X0) sF0)
       grind)
    | exact superpose eq10 eq52876
    | exact resolve eq52876 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52876
  have eq53269 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x X0))) = (M.op X1 (σ (M.op (M.op (M.op x X0) (M.op x y)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq53230 X1 X1
       have i₂ := eq669 x X1 sF0
       grind)
    | exact superpose eq669 eq53230
    | exact resolve eq53230 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq53230
  have eq53297 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x X0))) = (M.op X1 (σ (M.op (k (M.op x X0) y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq14860 eq53269
    | exact resolve eq53269 eq14860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53269
  have eq68629 : (k (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq20723
    | (have j0 := eq20723 (M.op x y)
       grind)
    | exact resolve eq20723 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20723
  have eq68630 : (k (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq68629
    | exact resolve eq68629 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68629
  have eq68699 : (k (σ (M.op x y)) (σ y)) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13432 eq68630
    | exact resolve eq68630 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68630
  have eq68761 : (k (σ (M.op x y)) (σ y)) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq68699
    | exact resolve eq68699 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68699
  have eq68927 : (k (σ (M.op x y)) (σ y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq68761
       have i₂ := eq7037 sF1 sF3
       grind)
    | exact superpose eq7037 eq68761
    | (have j1 := eq7037 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq68761
       have r₂ := eq7037 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq68761 eq7037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68761
  have eq68930 : (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq68927
  have eq68932 : (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7250 eq68930
    | exact resolve eq68930 eq7250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7250 eq68930
  have eq70064 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq68932 eq18835
    | (have j0 := eq18835 (σ (M.op x y)) x
       grind)
    | exact resolve eq18835 eq68932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18835
  have eq70069 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq18330 eq70064
    | exact resolve eq70064 eq18330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18330 eq70064
  have eq70070 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq13432 eq70069
    | (have j0 := eq70069 X0
       grind)
    | exact resolve eq70069 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70069
  have eq71800 : (k (M.op x (M.op x y)) (M.op x y)) = (k (M.op x (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq7430 eq48356
    | exact resolve eq48356 eq7430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48356
  have eq71822 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq7414 eq71800
    | exact resolve eq71800 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71800
  have eq71858 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq71822 eq37
    | exact resolve eq37 eq71822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq71822
  have eq71864 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq41 eq71858
    | exact resolve eq71858 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71858
  have eq71868 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq71864
    | exact resolve eq71864 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71864
  have eq71871 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq13432 eq71868
    | exact resolve eq71868 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71868
  have eq72376 : ∀ X0 : G, (M.op (M.op x X0) y) ≠ (M.op (M.op x X0) y) ∨ (M.op (M.op (M.op x y) (M.op x X0)) y) = (k (M.op (M.op x y) (M.op x X0)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq202 (M.op x X0)
       have i₂ := eq7341 X0
       grind)
    | exact superpose eq7341 eq202
    | (have j0 := eq202 (M.op x X0)
       grind)
    | (have r₁ := eq202 (M.op x X0)
       have r₂ := eq7341 X0
       grind)
    | exact resolve eq202 eq7341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq72408 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x X0)) y) = (k (M.op (M.op x y) (M.op x X0)) (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq72376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72376
  have eq72439 : ∀ X0 : G, (M.op (M.op (M.op x y) y) y) = (k (M.op (M.op x y) y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq72408 x
       have i₂ := eq7240 sF0 x
       grind)
    | exact superpose eq7240 eq72408
    | exact resolve eq72408 eq7240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7240 eq72408
  have eq72484 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) y) = (k (M.op (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq72439 X0
       have i₂ := eq7310 sF0
       grind)
    | exact superpose eq7310 eq72439
    | exact resolve eq72439 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72439
  have eq72528 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) y) = (k (k (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq72484 X0
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq72484
    | exact resolve eq72484 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72484
  have eq72567 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq72528 X0
       have i₂ := eq7310 (k sF0 sF0)
       grind)
    | exact superpose eq7310 eq72528
    | exact resolve eq72528 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72528
  have eq72598 : ∀ X0 : G, (k (k (M.op x y) (M.op x y)) y) = (k (k (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq13724 eq72567
    | exact resolve eq72567 eq13724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13724 eq72567
  have eq72616 : ∀ X0 : G, (k (k (M.op x y) (M.op x y)) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq25017 eq72598
    | exact resolve eq72598 eq25017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25017 eq72598
  have eq73031 : ∀ X0 : G, (σ (k (k (M.op x y) (M.op x y)) (M.op x y))) = (k (k (σ (M.op x y)) (σ y)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq72616 eq13426
    | exact resolve eq13426 eq72616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13426 eq72616
  have eq73036 : ∀ X0 : G, (k (σ (k (M.op x y) (M.op x y))) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ y)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq41 eq73031
    | exact resolve eq73031 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73031
  have eq73039 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ y)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq41 eq73036
    | exact resolve eq73036 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73036
  have eq73041 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ y)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq20 eq73039
    | (have j0 := eq73039 X0
       grind)
    | exact resolve eq73039 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73039
  have eq73043 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ y)) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ y)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq13432 eq73041
    | exact resolve eq73041 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73041
  have eq73045 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ y)) (σ y)) = (k (k (σ (M.op x y)) (σ y)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq25045 eq73043
    | exact resolve eq73043 eq25045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73043
  have eq103883 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x y) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8673 eq51849
    | (have j0 := eq51849 (σ (M.op x y))
       grind)
    | exact resolve eq51849 eq8673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51849
  have eq103938 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13432 eq103883
    | exact resolve eq103883 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103883
  have eq103947 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8673 eq103938
    | exact resolve eq103938 eq8673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8673 eq103938
  have eq103954 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (k x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq103947
       have r₂ := eq27
       grind)
    | exact resolve eq103947 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103947
  have eq103968 : (τ (σ x)) = (k (M.op x y) y) ∨ x = (k x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq103954 eq132
    | exact resolve eq132 eq103954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103954
  have eq104038 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (k x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13338 eq103968
    | exact resolve eq103968 eq13338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103968
  have eq104057 : x = (k (M.op x y) (M.op x y)) ∨ x = (k x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq104038
    | exact resolve eq104038 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104038
  have eq104058 : x = (k (M.op x y) (M.op x y)) ∨ x = (k x y) := by grind
  clear eq104057
  have eq104099 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ x = (k x y) := by
    first
    | exact superpose eq104058 eq47085
    | exact resolve eq47085 eq104058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47085
  have eq104119 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k x y) := by
    first
    | exact superpose eq104058 eq41
    | exact resolve eq41 eq104058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq104058
  have eq104138 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq104119
    | exact resolve eq104119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104119
  have eq104146 : (M.op x y) = (k x (M.op x y)) ∨ x = (k x y) := by
    first
    | exact superpose eq7414 eq104099
    | exact resolve eq104099 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104099
  have eq104170 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq13432 eq104138
    | exact resolve eq104138 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104138
  have eq104184 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq104170
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq104170
    | exact resolve eq104170 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104170
  have eq104222 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x y) := by
    first
    | exact superpose eq104146 eq35
    | exact resolve eq35 eq104146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104146
  have eq104229 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq104222
    | exact resolve eq104222 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104222
  have eq104478 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x y) := by
    first
    | exact superpose eq104184 eq25045
    | exact resolve eq25045 eq104184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104184
  have eq104512 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x y) := by
    first
    | exact superpose eq30575 eq104478
    | exact resolve eq104478 eq30575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30575 eq104478
  have eq104536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq104229 eq104512
    | exact resolve eq104512 eq104229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104229 eq104512
  have eq104553 : x = (k x y) := by
    first
    | (have r₁ := eq104536
       have r₂ := eq27
       grind)
    | exact resolve eq104536 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104536
  have eq104572 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq104553
       grind)
    | exact superpose eq104553 eq40
    | exact resolve eq40 eq104553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq104574 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq104572
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq104572
    | exact resolve eq104572 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104572
  have eq111500 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op (M.op (M.op X1 X0) X2) X0) = (k (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq691 X0 X0 X1 X2
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq691
    | (have j0 := eq691 X0 X0 X1 X2
       grind)
    | (have r₁ := eq691 X0 X0 X2 x
       have r₂ := eq182 X0
       grind)
    | exact resolve eq691 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111739 : ∀ X0 X1 : G, x ≠ (k y y) ∨ (k (M.op (M.op X0 (M.op x y)) X1) y) = (M.op (M.op (M.op X0 (M.op x y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq7430 eq691
    | (have j0 := eq691 y (M.op x y) X0 X1
       grind)
    | exact resolve eq691 eq7430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq111805 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) X0) = (k (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq111500 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111500
  have eq111848 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op x y)) X1) y) = (M.op (M.op (M.op X0 (M.op x y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have j0 := eq111739 X0 X1
       grind)
    | (have r₁ := eq111739 X0 X1
       have r₂ := eq7227
       grind)
    | exact resolve eq111739 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7227 eq111739
  have eq112038 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op x y)) X1) y) = (k (M.op (M.op X0 (M.op x y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq111848 X1 x
       have i₂ := eq111805 sF0 X1 x
       grind)
    | exact superpose eq111805 eq111848
    | exact resolve eq111848 eq111805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111805 eq111848
  have eq112280 : ∀ X0 : G, (k (M.op x X0) y) = (k (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7430 eq112038
    | exact resolve eq112038 eq7430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7430 eq112038
  have eq113030 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x X0))) = (M.op X1 (σ (M.op (k (M.op x X0) (M.op x y)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq53297 X0 X1
       have i₂ := eq112280 X0
       grind)
    | exact superpose eq112280 eq53297
    | exact resolve eq53297 eq112280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53297
  have eq151772 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X0 y) = (k X0 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq665 x X2 X1
       have i₂ := eq7351 X0 X2
       grind)
    | (have i₁ := eq665 X0 X1 X2
       have i₂ := eq7351 (k (M.op X0 X1) (M.op X0 X1)) X1
       grind)
    | exact superpose eq7351 eq665
    | (have j1 := eq7351 X0 X2
       grind)
    | exact resolve eq665 eq7351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq7351
  have eq151831 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x y)) = (k X0 (M.op x X2)) ∨ (M.op X1 X0) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151772 X0 X1 X2
       have i₂ := eq7310 X0
       grind)
    | exact superpose eq7310 eq151772
    | (have j0 := eq151772 X0 X1 X2
       grind)
    | exact resolve eq151772 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151772
  have eq151900 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (M.op X1 X0) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq7414 eq151831
    | (have j0 := eq151831 X0 X1 y
       grind)
    | exact resolve eq151831 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152254 : ∀ X0 X1 : G, (σ (M.op x (M.op x y))) = (k (σ x) (σ (M.op x X0))) ∨ (M.op X1 X0) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op x X0)
       have i₂ := eq151831 x X1 X0
       grind)
    | exact superpose eq151831 eq35
    | (have j1 := eq151831 X0 X1 x
       grind)
    | exact resolve eq35 eq151831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151831
  have eq152320 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op x X0))) ∨ (M.op X1 X0) = (M.op X1 x) := by
    intro X0 X1
    first
    | exact superpose eq7414 eq152254
    | (have j0 := eq152254 X0 X1
       grind)
    | exact resolve eq152254 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152254
  have eq152542 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op x X0))) ∨ (M.op X1 X0) = (M.op X1 x) := by
    intro X0 X1
    first
    | exact superpose eq20 eq152320
    | (have j0 := eq152320 X0 X1
       grind)
    | exact resolve eq152320 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152320
  have eq152897 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7414
       have i₂ := eq151900 sF0 x
       grind)
    | exact superpose eq151900 eq7414
    | (have j1 := eq151900 x X0
       grind)
    | exact resolve eq7414 eq151900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151900
  have eq153452 : ∀ X0 : G, (M.op X0 (σ (M.op x (M.op x y)))) = (M.op X0 (σ (M.op (k (M.op x (M.op x y)) (M.op x y)) x))) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq113030 x x
       have i₂ := eq152897 x
       grind)
    | exact superpose eq152897 eq113030
    | exact resolve eq113030 eq152897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113030
  have eq153464 : (M.op y (M.op x y)) ≠ (M.op y (M.op x y)) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq7429 x
       have i₂ := eq152897 y
       grind)
    | exact superpose eq152897 eq7429
    | (have j0 := eq7429 (M.op x y)
       grind)
    | (have r₁ := eq7429 x
       have r₂ := eq152897 y
       grind)
    | exact resolve eq7429 eq152897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7429 eq152897
  have eq153582 : (k x x) = (k x y) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq153464
  have eq153602 : (M.op x y) = (k x (M.op x y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq153582
       have i₂ := eq104553
       grind)
    | exact superpose eq104553 eq153582
    | exact resolve eq153582 eq104553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153582
  have eq153609 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ (M.op (k (M.op x y) (M.op x y)) x))) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7414 eq153452
    | exact resolve eq153452 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153452
  have eq153652 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ (M.op (k (M.op x y) (M.op x y)) x))) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq153609
    | (have j0 := eq153609 X0
       grind)
    | exact resolve eq153609 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153609
  have eq153676 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x x))) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7452 eq153652
    | exact resolve eq153652 eq7452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153652
  have eq153686 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ (k x x))) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq153676 X0
       have i₂ := eq182 x
       grind)
    | exact superpose eq182 eq153676
    | exact resolve eq153676 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153676
  have eq153692 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (σ x) (σ x))) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq153686 X0
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq153686
    | exact resolve eq153686 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq153686
  have eq153697 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (σ x) (σ x))) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq153692 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq153692
    | (have j0 := eq153692 X0
       grind)
    | exact resolve eq153692 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153692
  have eq153700 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7256 eq153697
    | exact resolve eq153697 eq7256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7256 eq153697
  have eq153714 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x x) := by
    first
    | exact superpose eq153602 eq35
    | exact resolve eq35 eq153602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153602
  have eq153725 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq153714
    | exact resolve eq153714 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153714
  have eq154112 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq153700 eq7658
    | (have j0 := eq7658 (σ y)
       grind)
    | (have r₁ := eq7658 (σ (M.op x y))
       have r₂ := eq153700 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq7658 eq153700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7658 eq153700
  have eq154142 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq154112
  have eq154150 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq13432 eq154142
    | exact resolve eq154142 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154142
  have eq154249 : (τ (k (σ (M.op x y)) (σ y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq154150 eq124
    | exact resolve eq124 eq154150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154254 : (k (M.op x y) y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq132 eq154249
    | exact resolve eq154249 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq154249
  have eq154255 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq13338 eq154254
    | exact resolve eq154254 eq13338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13338 eq154254
  have eq154256 : x = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq7452 eq154255
    | exact resolve eq154255 eq7452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154255
  have eq154277 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq154256 eq38
    | exact resolve eq38 eq154256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq154256
  have eq154279 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq20 eq154277
    | exact resolve eq154277 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154277
  have eq154292 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq154279
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq154279
    | exact resolve eq154279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154279
  have eq154331 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq154292 eq154150
    | exact resolve eq154150 eq154292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154150 eq154292
  have eq154344 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq154331
  have eq154376 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq154344 eq25045
    | exact resolve eq25045 eq154344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154386 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq154344 eq71871
    | exact resolve eq71871 eq154344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71871
  have eq154390 : ∀ X0 : G, (k (σ x) (σ y)) = (k (σ x) (σ (M.op x X0))) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq154344 eq73045
    | exact resolve eq73045 eq154344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73045 eq154344
  have eq154407 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op x X0))) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq104574 eq154390
    | exact resolve eq154390 eq104574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154390
  have eq154415 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq104574 eq154376
    | exact resolve eq154376 eq104574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154376
  have eq154473 : (τ (σ x)) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq154386 eq124
    | exact resolve eq124 eq154386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq154386
  have eq154476 : (M.op x y) = (k x (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq29 eq154473
    | exact resolve eq154473 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154473
  have eq157406 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq154415 eq163
    | exact resolve eq163 eq154415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq154415
  have eq157408 : (M.op x y) = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq29 eq157406
    | exact resolve eq157406 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157406
  have eq157695 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq154476 eq35
    | exact resolve eq35 eq154476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154476
  have eq157706 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq20 eq157695
    | exact resolve eq157695 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157695
  have eq157728 : x ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq157408
  have eq160297 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) (M.op x X0)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq154407 eq418
    | exact resolve eq418 eq154407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq154407
  have eq160303 : ∀ X0 : G, x = (k x (M.op x X0)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq29 eq160297
    | exact resolve eq160297 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160297
  have eq165614 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op X0 (M.op x y)) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq7414 eq152542
    | (have j0 := eq152542 y x
       grind)
    | exact resolve eq152542 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152542
  have eq166130 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq165614
    | (have j0 := eq165614 X0
       grind)
    | exact resolve eq165614 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165614
  have eq166372 : ∀ X0 : G, (k X0 x) = (M.op X0 (M.op x y)) ∨ (k x x) = X0 ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq7037 X0 x
       have i₂ := eq166130 X0
       grind)
    | exact superpose eq166130 eq7037
    | (have j0 := eq7037 X0 x
       grind)
    | exact resolve eq7037 eq166130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166130
  have eq166694 : ∀ X0 : G, (k X0 x) = (M.op X0 (M.op x y)) ∨ x = X0 ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq153725 eq166372
    | (have j0 := eq166372 X0
       grind)
    | exact resolve eq166372 eq153725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153725 eq166372
  have eq170316 : (k (k (M.op x y) x) y) = (M.op (k (M.op x y) x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq166694 eq14472
    | (have j1 := eq166694 (M.op x y)
       grind)
    | exact resolve eq14472 eq166694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14472 eq166694
  have eq170521 : (k x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq157706 eq170316
    | exact resolve eq170316 eq157706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157706 eq170316
  have eq170684 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq7414 eq170521
    | exact resolve eq170521 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170521
  have eq170788 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq170684
       have i₂ := eq104553
       grind)
    | exact superpose eq104553 eq170684
    | exact resolve eq170684 eq104553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170684
  have eq170789 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq170788
  have eq170972 : (τ (σ (M.op x y))) = (k x (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq170789 eq90
    | exact resolve eq90 eq170789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq170789
  have eq170997 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq170972
    | exact resolve eq170972 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170972
  have eq272335 : ∀ X0 : G, (k (M.op x y) (M.op x y)) ≠ (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x X0) (M.op x y)) = (k (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7384 sF0 x
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq7384
    | (have j0 := eq7384 (M.op x y) X0
       grind)
    | (have r₁ := eq7384 (M.op x y) x
       have r₂ := eq182 (M.op x y)
       grind)
    | exact resolve eq7384 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7384
  have eq272362 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (k (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq272335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272335
  have eq274242 : ∀ X0 : G, (k (k x X0) (M.op x y)) = (M.op (k x X0) (M.op x y)) ∨ x = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq272362 x
       have i₂ := eq7037 x x
       grind)
    | exact superpose eq7037 eq272362
    | (have j1 := eq7037 (k x X0) (M.op x y)
       grind)
    | exact resolve eq272362 eq7037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7037 eq272362
  have eq277924 : ∀ X0 : G, (k x (M.op x y)) = (M.op x (M.op x y)) ∨ x = (k (M.op x X0) (M.op x X0)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq274242 (M.op x X0)
       have i₂ := eq160303 X0
       grind)
    | exact superpose eq160303 eq274242
    | (have j0 := eq274242 (M.op x X0)
       grind)
    | exact resolve eq274242 eq160303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160303 eq274242
  have eq278108 : ∀ X0 : G, (M.op x y) = (k x (M.op x y)) ∨ x = (k (M.op x X0) (M.op x X0)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7414 eq277924
    | (have j0 := eq277924 X0
       grind)
    | exact resolve eq277924 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7414 eq277924
  have eq278109 : ∀ X0 : G, (M.op x y) = (k x (M.op x y)) ∨ x = (k (M.op x X0) (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq278108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278108
  have eq278125 : ∀ X0 : G, x = (M.op (M.op x X0) y) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq278109 X0
       have i₂ := eq7341 X0
       grind)
    | exact superpose eq7341 eq278109
    | exact resolve eq278109 eq7341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7341 eq278109
  have eq278137 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq278125 X0
       have i₂ := eq7310 (M.op x X0)
       grind)
    | exact superpose eq7310 eq278125
    | exact resolve eq278125 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7310 eq278125
  have eq278143 : ∀ X0 : G, x = (k (M.op x X0) y) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq14860 eq278137
    | exact resolve eq278137 eq14860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14860 eq278137
  have eq278146 : ∀ X0 : G, x = (k (M.op x X0) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq278143 X0
       have i₂ := eq112280 X0
       grind)
    | exact superpose eq112280 eq278143
    | exact resolve eq278143 eq112280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112280 eq278143
  have eq278149 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op x y) X0) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq170997 eq278146
    | exact resolve eq278146 eq170997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170997 eq278146
  have eq278167 : (M.op x y) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq278149 sF0
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq278149
    | exact resolve eq278149 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278149
  have eq278560 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq7452 eq278167
    | exact resolve eq278167 eq7452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7452 eq278167
  have eq278561 : (M.op x y) = (k x (M.op x y)) := by grind
  clear eq278560
  have eq278582 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq278561 eq35
    | exact resolve eq35 eq278561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq278594 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq278582
    | exact resolve eq278582 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278582
  have eq278608 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq278594 eq7702
    | (have j0 := eq7702 (σ (M.op x y)) x
       grind)
    | exact resolve eq7702 eq278594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7702
  have eq278624 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq278594 eq1000
    | (have j0 := eq1000 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq1000 eq278594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq278625 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq13432 eq278624
    | exact resolve eq278624 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278624
  have eq278632 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq13432 eq278608
    | (have j0 := eq278608 X0
       grind)
    | exact resolve eq278608 eq13432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13432 eq278608
  have eq282216 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq278625 eq25045
    | exact resolve eq25045 eq278625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25045 eq278625
  have eq282263 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq278594 eq282216
    | exact resolve eq282216 eq278594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282216
  have eq282286 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq104574 eq282263
    | exact resolve eq282263 eq104574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282263
  have eq282310 : (τ (σ (M.op x y))) = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq282286 eq97
    | exact resolve eq97 eq282286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq282286
  have eq282464 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq28 eq282310
    | exact resolve eq282310 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282310
  have eq282619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq282464 eq70070
    | exact resolve eq70070 eq282464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70070
  have eq282636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq282464 eq278632
    | exact resolve eq278632 eq282464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278632 eq282464
  have eq282692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by grind
  clear eq282619
  have eq282712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq26 eq282636
    | exact resolve eq282636 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282636
  have eq282724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq26 eq282692
    | exact resolve eq282692 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282692
  have eq282757 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq282712
       have r₂ := eq27
       grind)
    | exact resolve eq282712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282712
  have eq282769 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq282724
       have r₂ := eq27
       grind)
    | exact resolve eq282724 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282724
  have eq282791 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq282757 eq282769
    | exact resolve eq282769 eq282757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282757 eq282769
  have eq282813 : (M.op x y) ≠ (M.op x y) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9282
       have i₂ := eq282791
       grind)
    | exact superpose eq282791 eq9282
    | (have r₁ := eq9282
       have r₂ := eq282791
       grind)
    | exact resolve eq9282 eq282791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9282
  have eq282893 : x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq282813
  have eq282993 : x ≠ x ∨ (k x x) = (k x y) ∨ y = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13389 x
       have i₂ := eq282893
       grind)
    | exact superpose eq282893 eq13389
    | (have j0 := eq13389 x
       grind)
    | (have r₁ := eq13389 x
       have r₂ := eq282893
       grind)
    | exact resolve eq13389 eq282893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13389 eq282893
  have eq282996 : (k x x) = (k x y) ∨ y = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq282993
  have eq283001 : x = (k x x) ∨ y = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq282996
       have i₂ := eq104553
       grind)
    | exact superpose eq104553 eq282996
    | exact resolve eq282996 eq104553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282996
  have eq283005 : x = (M.op x y) ∨ y = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq282791 eq283001
    | exact resolve eq283001 eq282791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283001
  have eq283006 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq282791 eq283005
    | exact resolve eq283005 eq282791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282791 eq283005
  have eq284483 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq283006 eq68932
    | exact resolve eq68932 eq283006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68932 eq283006
  have eq284593 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq284483
  have eq284631 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq278594 eq284593
    | exact resolve eq284593 eq278594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284593
  have eq284749 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104574 eq284631
    | exact resolve eq284631 eq104574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104574 eq284631
  have eq284750 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq284749
  have eq284807 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq284750 eq28
    | exact resolve eq28 eq284750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq284750
  have eq285191 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq284807
    | exact resolve eq284807 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq284807
  have eq285192 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq285191
  have eq285430 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104553
       have i₂ := eq285192
       grind)
    | exact superpose eq285192 eq104553
    | exact resolve eq104553 eq285192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104553 eq285192
  have eq285501 : x = (k x (M.op x y)) := by
    first
    | (have r₁ := eq285430
       have r₂ := eq157728
       grind)
    | exact resolve eq285430 eq157728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157728 eq285430
  have eq285563 : x = (M.op x y) := by
    first
    | exact superpose eq278561 eq285501
    | exact resolve eq285501 eq278561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285501
  have eq285603 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq285563
       grind)
    | exact superpose eq285563 eq22
    | exact resolve eq22 eq285563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq285830 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq278561
       have i₂ := eq285563
       grind)
    | exact superpose eq285563 eq278561
    | exact resolve eq278561 eq285563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278561
  have eq285946 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq285603 eq20
    | exact resolve eq20 eq285603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285603
  have eq286586 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq285946 eq278594
    | exact resolve eq278594 eq285946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278594 eq285946
  have eq287100 : (M.op (k x x) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq286586 eq11221
    | exact resolve eq11221 eq286586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11221 eq286586
  have eq287219 : (τ (M.op (σ x) (σ y))) = (M.op (k x x) (M.op x y)) := by
    first
    | exact superpose eq26 eq287100
    | exact resolve eq287100 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq287100
  have eq287247 : (M.op (k (M.op x y) (M.op x y)) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq287219
       have i₂ := eq285563
       grind)
    | exact superpose eq285563 eq287219
    | exact resolve eq287219 eq285563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285563 eq287219
  have eq287261 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq285830 eq287247
    | exact resolve eq287247 eq285830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287247
  have eq287270 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq287261
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq287261
    | exact resolve eq287261 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq287261
  have eq287276 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq285830 eq287270
    | exact resolve eq287270 eq285830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285830 eq287270
  have eq287326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq287276 eq14
    | exact resolve eq14 eq287276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287276
  have eq287363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq287326
    | exact resolve eq287326 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq287326
  have eq287376 : False := by grind
  exact eq287376

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
       have j1 := eq14 (M.op X1 X0) (k X1 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq72 (σ X1) (σ X0)
       grind)
    | exact superpose eq72 eq15
    | (have j1 := eq72 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq72 X1 (τ X0)
       grind)
    | exact superpose eq72 eq18
    | (have j1 := eq72 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq72
  have eq401 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq425 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq401 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq401
    | (have j0 := eq401 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq401 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq734 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq16
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq763 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq734
       have i₂ := eq425 x y
       grind)
    | exact superpose eq425 eq734
    | (have j1 := eq425 (σ x) (σ y)
       grind)
    | (have r₁ := eq734
       have r₂ := eq425 x y
       grind)
    | (have r₁ := eq734
       have r₂ := eq425 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq734
       have r₂ := eq425 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq734 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq734
  have eq764 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq763
  have eq806 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq764
       grind)
    | exact superpose eq764 eq10
    | exact resolve eq10 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq837 : x = y ∨ x = y := by
    first
    | (have i₁ := eq806
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq806
    | exact resolve eq806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq838 : x = y := by grind
  clear eq837
  have eq840 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq838
       grind)
    | exact superpose eq838 eq16
    | exact resolve eq16 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq841 : False := by grind
  exact eq841

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pyx_pxx_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq79 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 (σ X0) X1 (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq21
    | exact resolve eq21 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq67 (M.op X0 X0)
       grind)
    | exact superpose eq67 eq131
    | exact resolve eq131 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq343 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 (τ X0) X1
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq360 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq343 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq343
    | (have j0 := eq343 X0 X1
       grind)
    | exact resolve eq343 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq366 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq360 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq360 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq360 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq370 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq366
    | (have j0 := eq366 X0 X1
       grind)
    | exact resolve eq366 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq694 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq370
    | (have j0 := eq370 X1 (τ X0)
       grind)
    | exact resolve eq370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq370 (σ X1) X0
       grind)
    | exact superpose eq370 eq15
    | (have j1 := eq370 (σ X1) X0
       grind)
    | exact resolve eq15 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq725 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq706 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq706
    | (have j0 := eq706 X0 X1
       grind)
    | exact resolve eq706 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq730 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq694
    | (have j0 := eq694 X0 X1
       grind)
    | exact resolve eq694 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq694
  have eq759 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq730 X0 (τ X1)
       grind)
    | exact superpose eq730 eq17
    | (have j1 := eq730 X0 (τ X1)
       grind)
    | exact resolve eq17 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq730
  have eq768 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq759 X0 X1
       have i₂ := eq103 X1
       grind)
    | exact superpose eq103 eq759
    | (have j0 := eq759 X0 X1
       grind)
    | exact resolve eq759 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq759
  have eq2249 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq768 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq768
    | (have j0 := eq768 X1 (σ X0)
       grind)
    | exact resolve eq768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq2304 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2249 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2249
    | (have j0 := eq2249 X0 X1
       grind)
    | exact resolve eq2249 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249
  have eq2308 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2304 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq2304
    | (have j0 := eq2304 X0 X1
       grind)
    | exact resolve eq2304 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304
  have eq2309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2308 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2308
    | (have j0 := eq2308 X0 X1
       grind)
    | exact resolve eq2308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq3025 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq725 x y
       grind)
    | exact superpose eq725 eq16
    | (have j1 := eq725 x y
       grind)
    | exact resolve eq16 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq3083 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3025
       have i₂ := eq2309 y x
       grind)
    | exact superpose eq2309 eq3025
    | (have j1 := eq2309 x y
       grind)
    | (have r₁ := eq3025
       have r₂ := eq2309 y x
       grind)
    | exact resolve eq3025 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309 eq3025
  have eq3084 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3083
  have eq3192 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq185 y x
       have i₂ := eq3084
       grind)
    | exact superpose eq3084 eq185
    | exact resolve eq185 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3204 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 y X0 y
       have i₂ := eq3084
       grind)
    | exact superpose eq3084 eq21
    | exact resolve eq21 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084
  have eq3209 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3204 X0 x
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq3204
    | exact resolve eq3204 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3204
  have eq3220 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3192 X0
       have i₂ := eq185 x X0
       grind)
    | exact superpose eq185 eq3192
    | exact resolve eq3192 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq3192
  have eq3233 : ∀ X0 : G, (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3209 X0
       grind)
    | exact superpose eq3209 eq10
    | (have j1 := eq3209 X0
       grind)
    | exact resolve eq10 eq3209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3209
  have eq3280 : ∀ X0 : G, (M.op x x) = (M.op y y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3233 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq3233
    | (have j0 := eq3233 X0
       grind)
    | exact resolve eq3233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3233
  have eq3405 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 y X0 y
       have i₂ := eq3280 X2
       grind)
    | exact superpose eq3280 eq21
    | (have j1 := eq3280 X2
       grind)
    | exact resolve eq21 eq3280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280
  have eq3411 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X2
    first
    | (have i₁ := eq3405 X0 x X2
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq3405
    | (have j0 := eq3405 X0 x X0
       grind)
    | exact resolve eq3405 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3405
  have eq3543 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3411 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3411
  have eq3544 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3543 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3543
  have eq6517 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X0)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 y X0
       have i₂ := eq3220 X1
       grind)
    | exact superpose eq3220 eq79
    | (have j1 := eq3220 X1
       grind)
    | exact resolve eq79 eq3220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3220
  have eq6586 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq6517 X0 X1
       have i₂ := eq79 x X0
       grind)
    | exact superpose eq79 eq6517
    | (have j0 := eq6517 X0 X0
       grind)
    | exact resolve eq6517 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq6517
  have eq7192 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq6586 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6586
  have eq7193 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq7192 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7192
  have eq7411 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7193 (σ x)
       grind)
    | exact superpose eq7193 eq16
    | exact resolve eq16 eq7193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7193
  have eq7447 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7411
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq7411
    | exact resolve eq7411 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq7411
  have eq7470 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7447
       have i₂ := eq3544 x
       grind)
    | exact superpose eq3544 eq7447
    | exact resolve eq7447 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544 eq7447
  have eq7471 : False := by grind
  exact eq7471

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_x_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  clear eq35
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  have eq56 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq58 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq72
    | exact resolve eq72 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq76
    | exact resolve eq76 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
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
  have eq86 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq87 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq96 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq202
    | exact resolve eq202 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq209 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq209
    | exact resolve eq209 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq458 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq99 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq99
    | (have j0 := eq99 (σ X0)
       grind)
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq99 x
       grind)
    | exact superpose eq99 eq43
    | (have j1 := eq99 x
       grind)
    | exact resolve eq43 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq463 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq87
    | (have j1 := eq99 y
       grind)
    | exact resolve eq87 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq99 sF3
       grind)
    | exact superpose eq99 eq104
    | (have j1 := eq99 (σ y)
       grind)
    | exact resolve eq104 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq3265 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq458 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq17491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq79 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq17491
    | exact resolve eq17491 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17491
  have eq17503 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq17492
       have r₂ := eq27
       grind)
    | exact resolve eq17492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17492
  have eq17505 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq17503
    | exact resolve eq17503 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17503
  have eq17508 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17505 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17505
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17505
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17505
       grind)
    | exact resolve eq12 eq17505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17512 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq17505 eq61
    | exact resolve eq61 eq17505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17516 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  have eq17518 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq213 eq17512
    | exact resolve eq17512 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17512
  have eq17522 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq17508
       have r₂ := eq26
       grind)
    | exact resolve eq17508 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17508
  have eq17549 : (k y y) = (τ (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17518 eq467
    | exact resolve eq467 eq17518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq17552 : (k y y) = (τ (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq17549
  have eq17569 : (τ (M.op (σ x) (σ y))) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17505 eq17552
    | exact resolve eq17552 eq17505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17505 eq17552
  have eq17617 : (τ (M.op (σ x) (σ y))) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq17569
  have eq17624 : (τ (M.op (σ x) (σ y))) = (k y y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq17617
       have r₂ := eq17516
       grind)
    | exact resolve eq17617 eq17516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17617
  have eq17890 : (k (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq17624
       grind)
    | exact superpose eq17624 eq87
    | exact resolve eq87 eq17624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq17624
  have eq17910 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq17890
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq17890
    | exact resolve eq17890 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17890
  have eq18857 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq17522
       have r₂ := eq17516
       grind)
    | exact resolve eq17522 eq17516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17516 eq17522
  have eq18863 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18857 eq79
    | exact resolve eq79 eq18857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq18857
  have eq18872 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq18863
  have eq18881 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq18872 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18872
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18872
       grind)
    | exact resolve eq13 eq18872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18872
  have eq18890 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq18881
  have eq18930 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq18890 eq55
    | exact resolve eq55 eq18890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18890
  have eq18950 : x = (k x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28 eq18930
    | exact resolve eq18930 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18930
  have eq18953 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq18950
       have r₂ := eq13 x y
       grind)
    | exact resolve eq18950 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18950
  have eq18956 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq18953 eq17518
    | exact resolve eq17518 eq18953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17518
  have eq18960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq18953 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq18953
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18953
       grind)
    | exact resolve eq12 eq18953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18953
  have eq18968 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq18960
  have eq18970 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ x = (k x y) := by grind
  clear eq18956
  have eq18972 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq18970
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq18970
       have r₂ := eq13 x y
       grind)
    | exact resolve eq18970 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18970
  have eq19096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq18968 eq17910
    | exact resolve eq17910 eq18968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17910 eq18968
  have eq19106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by grind
  clear eq19096
  have eq19116 : (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq19106
       have r₂ := eq27
       grind)
    | exact resolve eq19106 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19106
  have eq19132 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq19116
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq19116
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq19116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19116
  have eq19167 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | exact superpose eq19132 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19132
       grind)
    | exact resolve eq13 eq19132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19132
  have eq19176 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by grind
  clear eq19167
  have eq19185 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | exact superpose eq19176 eq55
    | exact resolve eq55 eq19176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19176
  have eq19206 : x = (k x y) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq19185
    | exact resolve eq19185 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19185
  have eq19207 : (M.op x y) = (M.op y x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq19206
  have eq19380 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 x X0 y
       have i₂ := eq19207
       grind)
    | exact superpose eq19207 eq61
    | exact resolve eq61 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19385 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq205 eq19380
    | exact resolve eq19380 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19380
  have eq19410 : (k (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq463
       have i₂ := eq19385 y
       grind)
    | exact superpose eq19385 eq463
    | exact resolve eq463 eq19385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19385
  have eq19415 : (k (σ y) (σ y)) = (σ (M.op y x)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq19410
       have r₂ := eq13 x y
       grind)
    | exact resolve eq19410 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19410
  have eq19683 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19415
       have i₂ := eq19207
       grind)
    | exact superpose eq19207 eq19415
    | exact resolve eq19415 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19415
  have eq19770 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq19683
  have eq19774 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq19770
    | exact resolve eq19770 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19770
  have eq20026 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19774
       have i₂ := eq99 sF3
       grind)
    | exact superpose eq99 eq19774
    | (have j1 := eq99 (σ y)
       grind)
    | exact resolve eq19774 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31993 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20026 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq20026
       grind)
    | exact resolve eq13 eq20026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20026
  have eq32003 : (σ y) = (k (σ y) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq31993
  have eq32913 : (σ (M.op x y)) = (σ y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32003 eq19774
    | exact resolve eq19774 eq32003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19774 eq32003
  have eq32933 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq32913
  have eq238479 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq18972
  have eq238485 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq238479
       have r₂ := eq19207
       grind)
    | exact resolve eq238479 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238479
  have eq238509 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq238485 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq238485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238485
  have eq238534 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq238509
       have r₂ := eq19207
       grind)
    | exact resolve eq238509 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19207 eq238509
  have eq238969 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq238534 eq55
    | exact resolve eq55 eq238534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238534
  have eq239054 : x = (k x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq238969
    | exact resolve eq238969 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238969
  have eq239055 : (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq239054
  have eq239087 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (k x y) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq239055
       grind)
    | exact superpose eq239055 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq239055
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq239055
       grind)
    | exact resolve eq12 eq239055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239088 : y ≠ (M.op x y) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq239055
       grind)
    | exact superpose eq239055 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq239055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239091 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ x = (k x y) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 x X0 y
       have i₂ := eq239055
       grind)
    | exact superpose eq239055 eq61
    | exact resolve eq61 eq239055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239095 : y ≠ (M.op x y) ∨ x = (k x y) := by grind
  clear eq239088
  have eq239122 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq205 eq239091
    | exact resolve eq239091 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239091
  have eq239124 : y = (M.op x y) ∨ (k x y) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq239087
       have r₂ := eq18
       grind)
    | exact resolve eq239087 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239087
  have eq239610 : (k (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq463
       have i₂ := eq239122 y
       grind)
    | exact superpose eq239122 eq463
    | exact resolve eq463 eq239122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq239717 : (k (σ y) (σ y)) = (σ (M.op y x)) ∨ x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq239610
       have r₂ := eq13 x y
       grind)
    | exact resolve eq239610 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239610
  have eq240663 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq239717
       have i₂ := eq239055
       grind)
    | exact superpose eq239055 eq239717
    | exact resolve eq239717 eq239055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239717
  have eq240869 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x y) := by grind
  clear eq240663
  have eq240875 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq240869
    | exact resolve eq240869 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240869
  have eq240882 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq240875
       have i₂ := eq99 sF3
       grind)
    | exact superpose eq99 eq240875
    | (have j1 := eq99 (σ y)
       grind)
    | exact resolve eq240875 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240875
  have eq245521 : (k x y) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq239124
       have r₂ := eq239095
       grind)
    | exact resolve eq239124 eq239095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239095 eq239124
  have eq245525 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq245521
       grind)
    | exact superpose eq245521 eq44
    | exact resolve eq44 eq245521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245521
  have eq245638 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq245525
       have i₂ := eq239122 y
       grind)
    | exact superpose eq239122 eq245525
    | exact resolve eq245525 eq239122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239122 eq245525
  have eq245838 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (k x y) := by grind
  clear eq245638
  have eq245844 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq245838
       have i₂ := eq239055
       grind)
    | exact superpose eq239055 eq245838
    | exact resolve eq245838 eq239055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239055
  have eq245862 : (τ (k (σ x) (σ y))) = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq245838
       grind)
    | exact superpose eq245838 eq16
    | exact resolve eq16 eq245838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245838
  have eq246056 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq245844
  have eq246057 : (k x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq55 eq245862
    | exact resolve eq245862 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245862
  have eq246064 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq246056
    | exact resolve eq246056 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246056
  have eq246095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq246064 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq246064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246064
  have eq246109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq246095
    | exact resolve eq246095 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246095
  have eq246121 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq246109
       have r₂ := eq27
       grind)
    | exact resolve eq246109 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246109
  have eq246124 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq246121
    | exact resolve eq246121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246121
  have eq248660 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq246057
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq246057
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq246057 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246057
  have eq248721 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq248660
  have eq248731 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq248721
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq248721
    | exact resolve eq248721 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248721
  have eq248741 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq248731
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq248731
    | exact resolve eq248731 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248731
  have eq249396 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq248741
       grind)
    | exact superpose eq248741 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq248741
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq248741
       grind)
    | exact resolve eq12 eq248741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249400 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 x X0 y
       have i₂ := eq248741
       grind)
    | exact superpose eq248741 eq61
    | exact resolve eq61 eq248741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249404 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  have eq249407 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq205 eq249400
    | exact resolve eq249400 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249400
  have eq249410 : y = (M.op x y) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq249396
       have r₂ := eq18
       grind)
    | exact resolve eq249396 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249396
  have eq260340 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq240882
  have eq260350 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq260340
       have r₂ := eq32933
       grind)
    | exact resolve eq260340 eq32933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32933 eq260340
  have eq268568 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    intro X0 X1
    first
    | exact superpose eq246124 eq61
    | exact resolve eq61 eq246124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268572 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by grind
  have eq268579 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq213 eq268568
    | exact resolve eq268568 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268568
  have eq884444 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq268579 eq260350
    | exact resolve eq260350 eq268579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260350 eq268579
  have eq884450 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq884444
  have eq886125 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq246124 eq884450
    | exact resolve eq884450 eq246124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246124 eq884450
  have eq886145 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq886125
  have eq886148 : x = (k x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq886145
       have r₂ := eq268572
       grind)
    | exact resolve eq886145 eq268572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268572 eq886145
  have eq886152 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq886148
       have r₂ := eq27
       grind)
    | exact resolve eq886148 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886148
  have eq886160 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq886152 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq886152
       grind)
    | exact resolve eq13 eq886152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886152
  have eq886174 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq886160
  have eq886189 : (τ (σ x)) = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq886174 eq55
    | exact resolve eq55 eq886174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq886174
  have eq886366 : x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq886189
    | exact resolve eq886189 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq886189
  have eq886367 : x = (k x y) := by grind
  clear eq886366
  have eq887994 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq886367
       grind)
    | exact superpose eq886367 eq44
    | exact resolve eq44 eq886367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq888083 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq887994
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq887994
    | exact resolve eq887994 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887994
  have eq888335 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq888083 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq888083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888354 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq888335
    | exact resolve eq888335 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888335
  have eq888380 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq888354
    | exact resolve eq888354 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888354
  have eq906088 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq888380 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq888380
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq888380
       grind)
    | exact resolve eq12 eq888380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906089 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq888380 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq888380
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq888380
       grind)
    | exact resolve eq12 eq888380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906093 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq888380 eq61
    | exact resolve eq61 eq888380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906102 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq888380
  have eq906104 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq213 eq906093
    | exact resolve eq906093 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq906093
  have eq906107 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq906089
       have r₂ := eq26
       grind)
    | exact resolve eq906089 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906089
  have eq906108 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq906088
       have r₂ := eq26
       grind)
    | exact resolve eq906088 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906088
  have eq906109 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq888083 eq906107
    | exact resolve eq906107 eq888083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888083 eq906107
  have eq906110 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq906108
    | exact resolve eq906108 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906108
  have eq906111 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq906110
  have eq919087 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq906104
    | (have j0 := eq906104 (σ x)
       grind)
    | exact resolve eq906104 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906104
  have eq919508 : (k y x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq906111 eq96
    | exact resolve eq96 eq906111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906111
  have eq919769 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq906109
       have r₂ := eq906102
       grind)
    | exact resolve eq906109 eq906102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906109
  have eq919781 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq919769 eq14
    | exact resolve eq14 eq919769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq922090 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq919087 eq919508
    | exact resolve eq919508 eq919087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919087 eq919508
  have eq922556 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq922090
  have eq922585 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq922556
       grind)
    | exact superpose eq922556 eq86
    | exact resolve eq86 eq922556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922556
  have eq922758 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq922585
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq922585
    | exact resolve eq922585 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922585
  have eq1096181 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq919769 eq919781
    | exact resolve eq919781 eq919769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919769 eq919781
  have eq1096380 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1096181
  have eq1096399 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq1096380
    | exact resolve eq1096380 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096380
  have eq1096425 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1096399 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq1096399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096399
  have eq1096440 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1096425
  have eq1096441 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1096440
  have eq1150829 : (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq249410
       have r₂ := eq249404
       grind)
    | exact resolve eq249410 eq249404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249410
  have eq1150830 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1150829
       have i₂ := eq886367
       grind)
    | exact superpose eq886367 eq1150829
    | exact resolve eq1150829 eq886367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886367 eq1150829
  have eq1150946 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq1150830
       grind)
    | exact superpose eq1150830 eq14
    | exact resolve eq14 eq1150830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1158591 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1150946 x
       have i₂ := eq1150830
       grind)
    | exact superpose eq1150830 eq1150946
    | exact resolve eq1150946 eq1150830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150946
  have eq1158794 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1158591
  have eq1158812 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1158794
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1158794
    | exact resolve eq1158794 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158794
  have eq1158886 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 x X0 x
       have i₂ := eq1158812
       grind)
    | exact superpose eq1158812 eq61
    | exact resolve eq61 eq1158812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158812
  have eq1158905 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq205 eq1158886
    | exact resolve eq1158886 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158886
  have eq1165288 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ y = (k y X0) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1158905 X0
       grind)
    | exact superpose eq1158905 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1158905 X0
       grind)
    | exact resolve eq13 eq1158905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158905
  have eq1904580 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1165288 y
       have i₂ := eq1150830
       grind)
    | exact superpose eq1150830 eq1165288
    | (have j0 := eq1165288 y
       grind)
    | (have r₁ := eq1165288 y
       have r₂ := eq1150830
       grind)
    | exact resolve eq1165288 eq1150830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150830 eq1165288
  have eq1904587 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1904580
  have eq1904588 : y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1904587
  have eq1904764 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99 y
       have i₂ := eq1904588
       grind)
    | exact superpose eq1904588 eq99
    | (have j0 := eq99 y
       grind)
    | exact resolve eq99 eq1904588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904588
  have eq1904815 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1904764
  have eq1904932 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1904815
       have i₂ := eq249407 y
       grind)
    | exact superpose eq249407 eq1904815
    | exact resolve eq1904815 eq249407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249407 eq1904815
  have eq1905083 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq1904932
  have eq1914877 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1905083
       have i₂ := eq248741
       grind)
    | exact superpose eq248741 eq1905083
    | exact resolve eq1905083 eq248741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248741 eq1905083
  have eq1915019 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq1914877
  have eq1915028 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1915019
       have r₂ := eq249404
       grind)
    | exact resolve eq1915019 eq249404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249404 eq1915019
  have eq1915151 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq1915028
       grind)
    | exact superpose eq1915028 eq14
    | exact resolve eq14 eq1915028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1934238 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1915151 x
       have i₂ := eq1915028
       grind)
    | exact superpose eq1915028 eq1915151
    | exact resolve eq1915151 eq1915028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915151
  have eq1934509 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1934238
  have eq1934534 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1934509
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1934509
    | exact resolve eq1934509 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934509
  have eq1934562 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq462
       have i₂ := eq1934534
       grind)
    | exact superpose eq1934534 eq462
    | exact resolve eq462 eq1934534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq1934619 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 x X0 x
       have i₂ := eq1934534
       grind)
    | exact superpose eq1934534 eq61
    | exact resolve eq61 eq1934534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934534
  have eq1934639 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1934562
  have eq1934640 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq205 eq1934619
    | exact resolve eq1934619 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq1934619
  have eq1934642 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1934639
    | exact resolve eq1934639 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934639
  have eq1939201 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1934642
       have i₂ := eq99 sF2
       grind)
    | exact superpose eq99 eq1934642
    | (have j1 := eq99 (σ x)
       grind)
    | exact resolve eq1934642 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1939238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1934642 eq1096441
    | exact resolve eq1096441 eq1934642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096441
  have eq1939303 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1939238
       have r₂ := eq27
       grind)
    | exact resolve eq1939238 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939238
  have eq1943660 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ y = (k y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1934640 X0
       grind)
    | exact superpose eq1934640 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1934640 X0
       grind)
    | exact resolve eq13 eq1934640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934640
  have eq2027653 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1943660 y
       have i₂ := eq1915028
       grind)
    | exact superpose eq1915028 eq1943660
    | (have j0 := eq1943660 y
       grind)
    | (have r₁ := eq1943660 y
       have r₂ := eq1915028
       grind)
    | exact resolve eq1943660 eq1915028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915028 eq1943660
  have eq2027654 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq2027653
  have eq2027655 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq2027654
  have eq2031391 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3265 y
       have i₂ := eq2027655
       grind)
    | exact superpose eq2027655 eq3265
    | (have j0 := eq3265 y
       grind)
    | exact resolve eq3265 eq2027655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027655
  have eq2031438 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2031391
  have eq2031478 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2031438
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2031438
    | exact resolve eq2031438 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031438
  have eq2035325 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2031478 eq14
    | exact resolve eq14 eq2031478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031478
  have eq2091697 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1939303 eq2035325
    | exact resolve eq2035325 eq1939303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939303
  have eq2091994 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2091697
  have eq2094170 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2091994 eq2035325
    | exact resolve eq2035325 eq2091994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035325 eq2091994
  have eq2094187 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2094170
  have eq2094229 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2094187
    | exact resolve eq2094187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094187
  have eq2094241 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2094229 eq1939201
    | exact resolve eq1939201 eq2094229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939201 eq2094229
  have eq2094264 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq2094241
  have eq2094274 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2094264
       have r₂ := eq27
       grind)
    | exact resolve eq2094264 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094264
  have eq2094276 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2094274 eq27
    | exact resolve eq27 eq2094274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2094277 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2094274 eq51
    | (have r₁ := eq51
       have r₂ := eq2094274
       grind)
    | exact resolve eq51 eq2094274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2094278 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2094274 eq57
    | exact resolve eq57 eq2094274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq2094303 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2094277
  have eq2096412 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2094303 eq96
    | exact resolve eq96 eq2094303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2094303
  have eq2096602 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2096412
    | exact resolve eq2096412 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2096412
  have eq2096611 : y = (k y x) := by
    first
    | (have r₁ := eq2096602
       have r₂ := eq50
       grind)
    | exact resolve eq2096602 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2096602
  have eq2096624 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq2096611
       grind)
    | exact superpose eq2096611 eq86
    | exact resolve eq86 eq2096611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2096611
  have eq2096844 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2096624
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2096624
    | exact resolve eq2096624 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2096624
  have eq2099446 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2096844 eq922758
    | exact resolve eq922758 eq2096844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922758 eq2096844
  have eq2099518 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2099446
       have r₂ := eq906102
       grind)
    | exact resolve eq2099446 eq906102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906102 eq2099446
  have eq2142279 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2094278
    | (have j0 := eq2094278 (σ y)
       grind)
    | exact resolve eq2094278 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094278
  have eq2142666 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2094274 eq2142279
    | exact resolve eq2142279 eq2094274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142279
  have eq2142689 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2142666
  have eq2144950 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2142689 eq61
    | exact resolve eq61 eq2142689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142689
  have eq2144977 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2144950 x X0
       have i₂ := eq61 X0 sF2 x sF3
       grind)
    | exact superpose eq61 eq2144950
    | exact resolve eq2144950 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2144950
  have eq2157714 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2144977
    | (have j0 := eq2144977 (σ x)
       grind)
    | exact resolve eq2144977 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2144977
  have eq2160135 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2157714 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2157714
       grind)
    | exact resolve eq13 eq2157714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157714
  have eq2160162 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2160135
       have r₂ := eq2094274
       grind)
    | exact resolve eq2160135 eq2094274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094274 eq2160135
  have eq2160243 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2160162 eq1934642
    | exact resolve eq1934642 eq2160162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934642 eq2160162
  have eq2160318 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2160243
  have eq2160366 : x = (M.op x y) := by
    first
    | (have r₁ := eq2160318
       have r₂ := eq2094276
       grind)
    | exact resolve eq2160318 eq2094276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094276 eq2160318
  have eq2172949 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2160366 eq20
    | exact resolve eq20 eq2160366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2172952 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq2160366 eq56
    | exact resolve eq56 eq2160366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2173579 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2172949
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2172949
    | exact resolve eq2172949 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172949
  have eq2173635 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2173579 eq26
    | exact resolve eq26 eq2173579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2174223 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2173579 eq2099518
    | exact resolve eq2099518 eq2173579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099518
  have eq2174242 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2174223
       have r₂ := eq27
       grind)
    | exact resolve eq2174223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174223
  have eq2194489 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq2174242 eq14
    | exact resolve eq14 eq2174242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2219877 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2172952 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2172952
    | (have j0 := eq2172952 y
       grind)
    | exact resolve eq2172952 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172952
  have eq2220220 : (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq2160366 eq2219877
    | exact resolve eq2219877 eq2160366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219877
  have eq2220427 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 y X0 y
       have i₂ := eq2220220
       grind)
    | exact superpose eq2220220 eq61
    | exact resolve eq61 eq2220220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220220
  have eq2220443 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2220427 X0 x
       have i₂ := eq61 x x X0 y
       grind)
    | exact superpose eq61 eq2220427
    | exact resolve eq2220427 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2220427
  have eq2220641 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2220443 x
       grind)
    | exact superpose eq2220443 eq18
    | (have j1 := eq2220443 x
       grind)
    | exact resolve eq18 eq2220443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2220443
  have eq2220777 : x = (M.op x x) := by
    first
    | exact superpose eq2160366 eq2220641
    | exact resolve eq2220641 eq2160366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160366 eq2220641
  have eq2221111 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq2220777
       grind)
    | exact superpose eq2220777 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq2220777
       grind)
    | exact resolve eq13 eq2220777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220777
  have eq2221127 : x = (k x x) := by grind
  clear eq2221111
  have eq2221230 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3265 x
       have i₂ := eq2221127
       grind)
    | exact superpose eq2221127 eq3265
    | (have j0 := eq3265 x
       grind)
    | exact resolve eq3265 eq2221127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3265 eq2221127
  have eq2221289 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2221230
  have eq2221331 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2221289
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2221289
    | exact resolve eq2221289 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2221289
  have eq2221387 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2173579 eq2221331
    | exact resolve eq2221331 eq2173579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173579 eq2221331
  have eq2257124 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2174242 eq2194489
    | exact resolve eq2194489 eq2174242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174242 eq2194489
  have eq2257518 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2221387 eq2257124
    | exact resolve eq2257124 eq2221387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221387 eq2257124
  have eq2257569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2173635 eq2257518
    | exact resolve eq2257518 eq2173635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173635 eq2257518
  have eq2257605 : False := by grind
  exact eq2257605

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq86
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq40 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq40
    | exact resolve eq40 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq198 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq200 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq198
    | exact resolve eq198 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq204 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq207 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq204 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq204
    | exact resolve eq204 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq406 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq44
    | (have j1 := eq106 x
       grind)
    | exact resolve eq44 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq106
  have eq15045 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15045
    | exact resolve eq15045 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15045
  have eq15057 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15046
       have r₂ := eq28
       grind)
    | exact resolve eq15046 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15046
  have eq15059 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15057
    | exact resolve eq15057 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15057
  have eq15061 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15059 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15059
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15059
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15059
       grind)
    | exact resolve eq12 eq15059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15064 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq15059 eq55
    | exact resolve eq55 eq15059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15059
  have eq15068 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq15061
  have eq15069 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq207 eq15064
    | exact resolve eq15064 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15064
  have eq15072 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15068
       have r₂ := eq27
       grind)
    | exact resolve eq15068 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15068
  have eq15074 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15069
    | (have j0 := eq15069 (σ x)
       grind)
    | exact resolve eq15069 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15069
  have eq15128 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  have eq15156 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15072 eq94
    | exact resolve eq94 eq15072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15072
  have eq15165 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq15156
  have eq15169 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15074 eq15165
    | exact resolve eq15165 eq15074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15074 eq15165
  have eq15182 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq15169
  have eq15185 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq15182
       have r₂ := eq15128
       grind)
    | exact resolve eq15182 eq15128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15128 eq15182
  have eq15186 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq15185
       have r₂ := eq28
       grind)
    | exact resolve eq15185 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15185
  have eq15433 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq15186
  have eq15444 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq27 eq15433
    | exact resolve eq15433 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15433
  have eq15452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq15444 eq94
    | exact resolve eq94 eq15444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq15444
  have eq15462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq15452
  have eq15465 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15462
       have r₂ := eq28
       grind)
    | exact resolve eq15462 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15462
  have eq15467 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq15465
       grind)
    | exact superpose eq15465 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15465
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15465
       grind)
    | exact resolve eq12 eq15465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15470 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 x X0 y
       have i₂ := eq15465
       grind)
    | exact superpose eq15465 eq55
    | exact resolve eq55 eq15465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15465
  have eq15474 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) := by grind
  clear eq15467
  have eq15475 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq200 eq15470
    | exact resolve eq15470 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq15470
  have eq15478 : (k y x) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15474
       have r₂ := eq19
       grind)
    | exact resolve eq15474 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15474
  have eq15730 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15475 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15475
    | (have j0 := eq15475 x
       grind)
    | exact resolve eq15475 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15475
  have eq15772 : y ≠ (M.op x y) ∨ y = (M.op x x) := by grind
  have eq15779 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq15478
       grind)
    | exact superpose eq15478 eq71
    | exact resolve eq71 eq15478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15478
  have eq15801 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15779
       have i₂ := eq15730
       grind)
    | exact superpose eq15730 eq15779
    | exact resolve eq15779 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15730 eq15779
  have eq15882 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15801
       have r₂ := eq15772
       grind)
    | exact resolve eq15801 eq15772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15772 eq15801
  have eq15883 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq15882
    | exact resolve eq15882 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15882
  have eq16145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15883 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq15883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq16145
    | exact resolve eq16145 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16145
  have eq16161 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16150
       have r₂ := eq28
       grind)
    | exact resolve eq16150 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16150
  have eq16163 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq16161
    | exact resolve eq16161 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16161
  have eq17192 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16163 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16163
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16163
       grind)
    | exact resolve eq12 eq16163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17195 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq16163 eq55
    | exact resolve eq55 eq16163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq16163
  have eq17199 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq17192
  have eq17200 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq207 eq17195
    | exact resolve eq17195 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq17195
  have eq17203 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17199
       have r₂ := eq27
       grind)
    | exact resolve eq17199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17199
  have eq49304 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17200
    | (have j0 := eq17200 (σ x)
       grind)
    | exact resolve eq17200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17200
  have eq49348 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  have eq49373 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17203 eq15883
    | exact resolve eq15883 eq17203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17203
  have eq49424 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq49373
  have eq49741 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq49304 eq49424
    | exact resolve eq49424 eq49304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49304 eq49424
  have eq49756 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq49741
  have eq49760 : y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq49756
       have r₂ := eq49348
       grind)
    | exact resolve eq49756 eq49348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49348 eq49756
  have eq49761 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq49760
       have r₂ := eq28
       grind)
    | exact resolve eq49760 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49760
  have eq49765 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq49761
  have eq49777 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq49765
    | exact resolve eq49765 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49765
  have eq49797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq49777 eq15883
    | exact resolve eq15883 eq49777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15883 eq49777
  have eq49849 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq49797
  have eq49858 : y = (M.op x x) := by
    first
    | (have r₁ := eq49849
       have r₂ := eq28
       grind)
    | exact resolve eq49849 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49849
  have eq50164 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq406
       have i₂ := eq49858
       grind)
    | exact superpose eq49858 eq406
    | exact resolve eq406 eq49858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq50165 : (M.op x y) = (k y x) := by grind
  have eq50167 : y ≠ y ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq49858
       grind)
    | exact superpose eq49858 eq12
    | exact resolve eq12 eq49858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49858
  have eq50173 : y = (k x x) ∨ x = y := by grind
  clear eq50167
  have eq50175 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq50165
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq50165
    | exact resolve eq50165 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq50165
  have eq50176 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq50164
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq50164
    | exact resolve eq50164 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50164
  have eq50180 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq50175
       grind)
    | exact superpose eq50175 eq71
    | exact resolve eq71 eq50175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50175
  have eq50210 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq50180
    | exact resolve eq50180 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq50180
  have eq50509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq50210 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq50210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq50509
    | exact resolve eq50509 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50509
  have eq50521 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq50510
       have r₂ := eq28
       grind)
    | exact resolve eq50510 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50510
  have eq50523 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq50521
    | exact resolve eq50521 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50521
  have eq50532 : (σ (k y x)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq147
       have i₂ := eq50173
       grind)
    | exact superpose eq50173 eq147
    | exact resolve eq147 eq50173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq50173
  have eq50555 : (k (σ y) (σ x)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq50532
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq50532
    | exact resolve eq50532 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq50532
  have eq50561 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq50210 eq50555
    | exact resolve eq50555 eq50210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50555
  have eq51890 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq50523 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq50523
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq50523
       grind)
    | exact resolve eq12 eq50523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50523
  have eq51897 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
  clear eq51890
  have eq51901 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq51897
       have r₂ := eq27
       grind)
    | exact resolve eq51897 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51897
  have eq51902 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq50210 eq51901
    | exact resolve eq51901 eq50210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51901
  have eq52195 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq51902
  have eq52206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq50210 eq52195
    | exact resolve eq52195 eq50210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50210 eq52195
  have eq52208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq52206
    | exact resolve eq52206 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52206
  have eq52209 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq52208
       have r₂ := eq28
       grind)
    | exact resolve eq52208 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52208
  have eq52504 : (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) := by grind
  have eq52506 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq52209 eq12
    | exact resolve eq12 eq52209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52512 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq52506
  have eq52816 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq50176 eq52512
    | exact resolve eq52512 eq50176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52828 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq52512 eq50561
    | exact resolve eq50561 eq52512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50561 eq52512
  have eq52832 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq52504 eq52828
    | exact resolve eq52828 eq52504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52828
  have eq53431 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq52816 eq27
    | exact resolve eq27 eq52816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52816
  have eq55836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq53431 eq52832
    | exact resolve eq52832 eq53431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52832 eq53431
  have eq55845 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq55836
  have eq55849 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq55845
       have r₂ := eq28
       grind)
    | exact resolve eq55845 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55845
  have eq55853 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq55849 eq29
    | exact resolve eq29 eq55849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq55967 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq55849 eq50176
    | exact resolve eq50176 eq55849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50176
  have eq55972 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq55849 eq52209
    | exact resolve eq52209 eq55849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55973 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq55849 eq52504
    | exact resolve eq52504 eq55849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52504 eq55849
  have eq55976 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq55967
  have eq56037 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq55853
    | exact resolve eq55853 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55853
  have eq56514 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq55973 eq55976
    | exact resolve eq55976 eq55973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55973 eq55976
  have eq56516 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq56514
  have eq56521 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq56516 eq55972
    | exact resolve eq55972 eq56516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55972 eq56516
  have eq56535 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq56521
  have eq56539 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq56535 eq30
    | exact resolve eq30 eq56535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq56535
  have eq56711 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq56539
    | exact resolve eq56539 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq56539
  have eq56893 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq56711 eq56037
    | exact resolve eq56037 eq56711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56037 eq56711
  have eq56898 : x = y := by grind
  clear eq56893
  have eq57044 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq56898
       grind)
    | exact superpose eq56898 eq25
    | exact resolve eq25 eq56898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq56898
  have eq57389 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq57044
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57044
    | exact resolve eq57044 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq57044
  have eq57468 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq57389 eq27
    | exact resolve eq27 eq57389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq57389
  have eq57645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52209 eq57468
    | exact resolve eq57468 eq52209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52209 eq57468
  have eq57656 : False := by grind
  exact eq57656

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pxy_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq42 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq102 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq102
    | (have j0 := eq102 X0 X1
       grind)
    | exact resolve eq102 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq138 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X2 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq44
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq138
    | exact resolve eq138 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq290 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106 x y
       grind)
    | exact superpose eq106 eq16
    | (have j1 := eq106 x y
       grind)
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq2046 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq290
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq290
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq290
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq290
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq290 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq2047 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq2046
  have eq15173 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2047
       grind)
    | exact superpose eq2047 eq16
    | exact resolve eq16 eq2047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq15174 : (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq15173
       have r₂ := eq22 x
       grind)
    | exact resolve eq15173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15173
  have eq15179 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq15174
       grind)
    | exact superpose eq15174 eq22
    | exact resolve eq22 eq15174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15174
  have eq15222 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq15179
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq15179
    | exact resolve eq15179 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15179
  have eq15223 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq15222
  have eq15247 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq15223
       grind)
    | exact superpose eq15223 eq10
    | exact resolve eq10 eq15223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15223
  have eq15296 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq15247
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq15247
    | exact resolve eq15247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15247
  have eq15297 : (M.op x x) = (M.op y y) := by grind
  clear eq15296
  have eq15587 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq171 y x
       have i₂ := eq15297
       grind)
    | exact superpose eq15297 eq171
    | exact resolve eq171 eq15297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15620 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 y X0 y
       have i₂ := eq15297
       grind)
    | exact superpose eq15297 eq44
    | exact resolve eq44 eq15297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15297
  have eq15632 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq15620 X0 x
       have i₂ := eq44 x x X0 x
       grind)
    | exact superpose eq44 eq15620
    | exact resolve eq15620 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq15620
  have eq15653 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15587 X0
       have i₂ := eq171 x X0
       grind)
    | exact superpose eq171 eq15587
    | exact resolve eq15587 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq15587
  have eq16533 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15653 (σ x)
       grind)
    | exact superpose eq15653 eq16
    | exact resolve eq16 eq15653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15653
  have eq16574 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16533
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq16533
    | exact resolve eq16533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16533
  have eq16651 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16574
       have i₂ := eq15632 x
       grind)
    | exact superpose eq15632 eq16574
    | exact resolve eq16574 eq15632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15632 eq16574
  have eq16652 : False := by grind
  exact eq16652

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  have eq50 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : (σ (k x (k x y))) = (k (σ x) (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq36 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq36
    | exact resolve eq36 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq59 : ∀ X0 : G, (σ (k X0 (k x y))) = (k (σ X0) (k (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq10
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq50 eq16
    | exact resolve eq16 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  have eq70 : x ≠ (M.op x y) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq98 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq94
  have eq99 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq98
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq120
  have eq124 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq123
  have eq130 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq16
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq163 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq222 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq222
    | exact resolve eq222 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq239 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq250 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq239 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq239
    | exact resolve eq239 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq251 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq250
  have eq519 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (σ X0) X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq57
    | exact resolve eq57 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq621 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq251 X0
       grind)
    | exact superpose eq251 eq16
    | exact resolve eq16 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq739 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (τ X0) X1 (τ X0)
       have i₂ := eq621 X0
       grind)
    | exact superpose eq621 eq57
    | exact resolve eq57 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq808
    | exact resolve eq808 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq812 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq809
       have r₂ := eq28
       grind)
    | exact resolve eq809 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq814 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq812
    | exact resolve eq812 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq816 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq814 eq71
    | (have r₁ := eq71
       have r₂ := eq814
       grind)
    | exact resolve eq71 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq817 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq814 eq225
    | exact resolve eq225 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq820 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq816
  have eq821 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq820
  have eq824 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq821 eq88
    | exact resolve eq88 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq825 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq821 eq61
    | exact resolve eq61 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq821
  have eq828 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq824
  have eq832 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq825
    | exact resolve eq825 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq835 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq832
       have r₂ := eq70
       grind)
    | exact resolve eq832 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq838 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq835
       grind)
    | exact superpose eq835 eq49
    | exact resolve eq49 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq843 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq838
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq838
    | exact resolve eq838 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq875 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq843 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq876 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq875
  have eq880 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq876
    | exact resolve eq876 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq883 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq880
    | exact resolve eq880 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq886 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq828 eq30
    | exact resolve eq30 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq905 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq886
    | exact resolve eq886 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq906 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq905
  have eq910 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq906 eq27
    | exact resolve eq27 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq906 eq30
    | exact resolve eq30 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq906 eq88
    | exact resolve eq88 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq918 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq906 eq130
    | exact resolve eq130 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq924 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq915
  have eq927 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq163 eq918
    | exact resolve eq918 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq918
  have eq933 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq911
    | exact resolve eq911 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq968 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq924 eq65
    | exact resolve eq65 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq924
  have eq970 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq968
    | exact resolve eq968 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq971 : y = (k x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq933 eq970
    | exact resolve eq970 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933 eq970
  have eq977 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq971
  have eq979 : y = (k x y) ∨ x = y := by
    first
    | (have r₁ := eq977
       have r₂ := eq70
       grind)
    | exact resolve eq977 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq977
  have eq981 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq979
       grind)
    | exact superpose eq979 eq49
    | exact resolve eq49 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq981
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq981
    | exact resolve eq981 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1046 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq883 eq28
    | exact resolve eq28 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq1050 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq906 eq1046
    | (have r₁ := eq1046
       have r₂ := eq906
       grind)
    | exact resolve eq1046 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1051 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1050
  have eq1052 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1051
  have eq1097 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1052 eq54
    | exact resolve eq54 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1155 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (M.op y y) X0)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq927 eq14
    | exact resolve eq14 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq1160 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1155 X0
       have i₂ := eq14 X0 y y
       grind)
    | exact superpose eq14 eq1155
    | exact resolve eq1155 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq9457 : (σ (k x y)) = (k (σ x) (k (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq58
       have i₂ := eq979
       grind)
    | exact superpose eq979 eq58
    | exact resolve eq58 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq979
  have eq9507 : (k (σ x) (σ y)) = (k (σ x) (k (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq9457
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq9457
    | exact resolve eq9457 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9457
  have eq9536 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9507
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq9507
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq9507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9507
  have eq9550 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq9536
    | exact resolve eq9536 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9536
  have eq9551 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq9550
    | exact resolve eq9550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9550
  have eq15425 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (k x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq986 eq59
    | exact resolve eq59 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq15455 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (k x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq41 eq15425
    | exact resolve eq15425 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq15425
  have eq15514 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (k x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35 X0 (k x y)
       have i₂ := eq15455 (τ X0)
       grind)
    | exact superpose eq15455 eq35
    | exact resolve eq35 eq15455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15455
  have eq15597 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (k (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq15514 X0
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq15514
    | exact resolve eq15514 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq15514
  have eq15613 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (k (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq15597 X0
       have i₂ := eq35 X0 y
       grind)
    | exact superpose eq35 eq15597
    | exact resolve eq15597 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq15597
  have eq15624 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (k (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq15613 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15613
    | (have j0 := eq15613 X0
       grind)
    | exact resolve eq15613 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15613
  have eq15754 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq15624 X0
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq15624
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq15624 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15624
  have eq15858 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq27 eq15754
    | (have j0 := eq15754 X0
       grind)
    | exact resolve eq15754 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15754
  have eq15867 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq27 eq15858
    | (have j0 := eq15858 X0
       grind)
    | exact resolve eq15858 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15858
  have eq31166 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15867 eq9551
    | exact resolve eq9551 eq15867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9551 eq15867
  have eq31179 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq31166
  have eq1185532 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq817
    | (have j0 := eq817 X0 (σ y)
       grind)
    | exact resolve eq817 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq1185889 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq814 eq1185532
    | exact resolve eq1185532 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq1185532
  have eq1186079 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1185889 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185889
  have eq1186088 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq906 eq1186079
    | exact resolve eq1186079 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq1186079
  have eq1186690 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1186088 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186088
  have eq1187209 : (M.op x x) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1186690 eq69
    | exact resolve eq69 eq1186690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186690
  have eq1188128 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq910 eq1187209
    | exact resolve eq1187209 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq1187209
  have eq1188654 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1188128
  have eq1188665 : (M.op (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq1188654
       grind)
    | exact superpose eq1188654 eq52
    | exact resolve eq52 eq1188654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188654
  have eq1188839 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1188665
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1188665
    | exact resolve eq1188665 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188665
  have eq1317804 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1188839 eq1097
    | exact resolve eq1097 eq1188839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq1188839
  have eq1318165 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1317804
  have eq1318183 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq1318165
    | exact resolve eq1318165 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318165
  have eq1318184 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1052 eq1318183
    | exact resolve eq1318183 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq1318183
  have eq1318216 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1318184
  have eq1318228 : (τ (σ x)) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1318216 eq69
    | exact resolve eq69 eq1318216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1318274 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) = (M.op X0 (M.op (τ (σ x)) X1)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1318216 eq739
    | exact resolve eq739 eq1318216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318216
  have eq1318319 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X1)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq1318274
    | exact resolve eq1318274 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318274
  have eq1318356 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1318228
    | exact resolve eq1318228 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318228
  have eq2285684 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1318319 X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1318319
    | (have j0 := eq1318319 X0 y
       grind)
    | exact resolve eq1318319 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318319
  have eq2286140 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2285684 eq1160
    | exact resolve eq1160 eq2285684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq2285684
  have eq2286708 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq2286140 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286140
  have eq2289816 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2286708 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2286708
    | (have j0 := eq2286708 x
       grind)
    | exact resolve eq2286708 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286708
  have eq2290637 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1318356
       have i₂ := eq2289816
       grind)
    | exact superpose eq2289816 eq1318356
    | exact resolve eq1318356 eq2289816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318356 eq2289816
  have eq2290671 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2290637
  have eq2290835 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2290671 eq29
    | exact resolve eq29 eq2290671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290671
  have eq2293267 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq2290835
    | exact resolve eq2290835 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290835
  have eq2293268 : x = (M.op x y) ∨ x = y := by grind
  clear eq2293267
  have eq2296321 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2293268 eq21
    | exact resolve eq21 eq2293268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2296323 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2293268 eq53
    | exact resolve eq53 eq2293268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2296339 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2293268 eq124
    | exact resolve eq124 eq2293268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq2297572 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq2296339
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq2296339
    | exact resolve eq2296339 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296339
  have eq2297587 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2296321
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2296321
    | exact resolve eq2296321 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296321
  have eq2297760 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2297587 eq27
    | exact resolve eq27 eq2297587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2297844 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2297587 eq986
    | exact resolve eq986 eq2297587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq2298295 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2297587 eq31179
    | exact resolve eq31179 eq2297587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31179 eq2297587
  have eq2299419 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2298295
  have eq2299671 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq2297844
  have eq2299723 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2299419
       have r₂ := eq28
       grind)
    | exact resolve eq2299419 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299419
  have eq2303793 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) = (M.op X0 (M.op (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq2297572 eq739
    | exact resolve eq739 eq2297572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297572
  have eq2303861 : ∀ X0 : G, (M.op X0 (τ (σ (M.op x y)))) = (M.op X0 (τ (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2303793 x x
       have i₂ := eq739 sF1 x x
       grind)
    | exact superpose eq739 eq2303793
    | exact resolve eq2303793 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq2303793
  have eq2303906 : ∀ X0 : G, (M.op X0 (τ (σ (M.op x y)))) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29 eq2303861
    | exact resolve eq2303861 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2303861
  have eq2303910 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq31 eq2303906
    | exact resolve eq2303906 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2303906
  have eq2334821 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2299723 eq2299671
    | exact resolve eq2299671 eq2299723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299671 eq2299723
  have eq2334911 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2334821
  have eq2336521 : (M.op y y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq2296323 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2296323
    | (have j0 := eq2296323 y
       grind)
    | exact resolve eq2296323 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296323
  have eq2336980 : (M.op y y) = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2336521 eq2303910
    | exact resolve eq2303910 eq2336521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2303910 eq2336521
  have eq2336996 : (M.op y y) = (M.op y x) ∨ x = y := by grind
  clear eq2336980
  have eq2337182 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 y X0 y
       have i₂ := eq2336996
       grind)
    | exact superpose eq2336996 eq57
    | exact resolve eq57 eq2336996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336996
  have eq2337211 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2337182 X0 x
       have i₂ := eq57 x x X0 y
       grind)
    | exact superpose eq57 eq2337182
    | exact resolve eq2337182 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2337182
  have eq2337894 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2337211 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2337211
    | (have j0 := eq2337211 x
       grind)
    | exact resolve eq2337211 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337211
  have eq2338633 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq2337894
       grind)
    | exact superpose eq2337894 eq52
    | exact resolve eq52 eq2337894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2338719 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq519 x X0 X1
       have i₂ := eq2337894
       grind)
    | exact superpose eq2337894 eq519
    | exact resolve eq519 eq2337894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq2337894
  have eq2338779 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq21 eq2338719
    | (have j0 := eq2338719 X0 X1
       grind)
    | exact resolve eq2338719 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338719
  have eq2338858 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq2338633
    | exact resolve eq2338633 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338633
  have eq2338876 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2338779 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2338779
    | (have j0 := eq2338779 X0 X1
       grind)
    | exact resolve eq2338779 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338779
  have eq2448204 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq2297760 eq2338876
    | exact resolve eq2338876 eq2297760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297760 eq2338876
  have eq2448668 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2448204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448204
  have eq2448676 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2334911 eq2448668
    | exact resolve eq2448668 eq2334911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334911 eq2448668
  have eq2448949 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2448676 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448676
  have eq2606274 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq2448949
    | (have j0 := eq2448949 (σ x)
       grind)
    | exact resolve eq2448949 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448949
  have eq2607093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2606274 eq2338858
    | exact resolve eq2338858 eq2606274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338858 eq2606274
  have eq2607192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2607093
  have eq2607217 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2607192
       have r₂ := eq28
       grind)
    | exact resolve eq2607192 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607192
  have eq2607864 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2607217 eq30
    | exact resolve eq30 eq2607217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2607217
  have eq2610656 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq2607864
    | exact resolve eq2607864 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2607864
  have eq2612090 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2610656 eq2293268
    | exact resolve eq2293268 eq2610656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2293268 eq2610656
  have eq2612659 : x = y := by grind
  clear eq2612090
  have eq2614875 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2612659
       grind)
    | exact superpose eq2612659 eq19
    | exact resolve eq19 eq2612659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2614876 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2612659
       grind)
    | exact superpose eq2612659 eq25
    | exact resolve eq25 eq2612659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2612659
  have eq2616081 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2614876
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2614876
    | exact resolve eq2614876 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2614876
  have eq2616254 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2616081 eq27
    | exact resolve eq27 eq2616081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2616081
  have eq2618794 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2616254 eq69
    | exact resolve eq69 eq2616254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2616254
  have eq2618957 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2618794
       have i₂ := eq2614875
       grind)
    | exact superpose eq2614875 eq2618794
    | exact resolve eq2618794 eq2614875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614875 eq2618794
  have eq2619052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2618957 eq15
    | exact resolve eq15 eq2618957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2618957
  have eq2619934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2619052
    | exact resolve eq2619052 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2619052
  have eq2620175 : False := by grind
  exact eq2620175
