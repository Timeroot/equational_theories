import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyy_y_pyx_Equation1043 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1043 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  clear eq24
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
  have eq50 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op X1 (M.op X0 X2)) X2) X0) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 (M.op X0 X2)) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X1 (M.op X0 X2)) X2) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X0 X2)) X2) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 (M.op X0 X2)) X2) X0) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq76 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ x = (k y x) := by
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
  have eq77 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq106
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq125 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq136 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ (k (k y (M.op x y)) (M.op x y))) = (k (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq75 eq41
    | exact resolve eq41 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq200 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq200
    | (have j0 := eq200 X0
       grind)
    | exact resolve eq200 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq205
    | (have j0 := eq205 X0
       grind)
    | exact resolve eq205 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq226 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (k (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq66
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (k (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq50 eq66
    | exact resolve eq66 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (k (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq431 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq431
    | (have j0 := eq431 X0
       grind)
    | exact resolve eq431 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq455 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq226 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq226
    | (have j0 := eq226 X0 x
       grind)
    | exact resolve eq226 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq490 : (k (k y x) x) = (τ (k (k (σ y) (σ x)) (σ x))) := by
    first
    | exact superpose eq83 eq455
    | exact resolve eq455 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq635 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y x X0 X1
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op (M.op X3 (M.op X0 X4)) X4)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op (M.op X3 (M.op X0 X4)) X4)
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
       have i₂ := eq52 X0 X1 X3 X4
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (k (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3)) (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq66
    | exact resolve eq66 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq652
    | exact resolve eq652 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq658 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 X1 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq651
    | exact resolve eq651 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq661 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq648 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq648
    | exact resolve eq648 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq667 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq657 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq657
    | (have j0 := eq657 y x
       grind)
    | exact resolve eq657 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq657
    | (have j0 := eq657 (σ y) (σ x)
       grind)
    | exact resolve eq657 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq667 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq667
       grind)
    | exact resolve eq13 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq667 eq14
    | exact resolve eq14 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq684
  have eq691 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq669 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq669
       grind)
    | exact resolve eq13 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq669 eq14
    | exact resolve eq14 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq697 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq691
  have eq699 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq690 eq75
    | exact resolve eq75 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq773 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1377 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X0)) = (k (M.op (M.op X2 (k X0 (M.op X1 X0))) (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (M.op X1 X0) X1 (M.op X1 X0)
       have i₂ := eq658 X0 X1
       grind)
    | exact superpose eq658 eq66
    | exact resolve eq66 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2124 : (k (k (σ y) (σ (M.op x y))) (σ (M.op x y))) = (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq690 eq191
    | exact resolve eq191 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq3586 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op (M.op X0 (M.op x y)) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq50 eq661
    | exact resolve eq661 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3593 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) X1)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) X1)) (M.op (σ y) (M.op (M.op X0 (M.op (σ y) X1)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq637 eq661
    | exact resolve eq661 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3596 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq661 X0 X0 x
       grind)
    | exact superpose eq661 eq52
    | exact resolve eq52 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3621 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) X1)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq3593 X1 x
       have i₂ := eq14 sF3 X1 x
       grind)
    | exact superpose eq14 eq3593
    | exact resolve eq3593 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593
  have eq3628 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op (M.op X0 (M.op x y)) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3586 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3586
    | (have j0 := eq3586 X0
       grind)
    | exact resolve eq3586 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq3642 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq637 sF3 sF3
       have i₂ := eq3596 sF3
       grind)
    | exact superpose eq3596 eq637
    | exact resolve eq637 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq3643 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq661 X0 X0 X0
       have i₂ := eq3596 X0
       grind)
    | exact superpose eq3596 eq661
    | exact resolve eq661 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3663 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3643 X0
       have i₂ := eq658 X0 X0
       grind)
    | exact superpose eq658 eq3643
    | exact resolve eq3643 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3643
  have eq3765 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq423 X0 X0 x X0
       have i₂ := eq661 X0 X0 x
       grind)
    | exact superpose eq661 eq423
    | exact resolve eq423 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq3852 : (σ (M.op (M.op x y) (M.op x y))) = (k (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2124
       have i₂ := eq3765 sF0
       grind)
    | exact superpose eq3765 eq2124
    | exact resolve eq2124 eq3765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq3855 : (k (σ y) (σ (M.op x y))) = (k (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq699 eq3852
    | exact resolve eq3852 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3852
  have eq4157 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op (M.op X1 (M.op X0 (M.op x y))) (M.op (k (M.op x y) (M.op X0 (M.op x y))) (M.op (M.op X2 (M.op (M.op X0 (M.op x y)) X3)) X3)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq439 eq639
    | exact resolve eq639 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4245 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op (M.op X1 (M.op x y)) (M.op y (M.op (M.op X2 (M.op y X3)) X3))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq635 eq639
    | exact resolve eq639 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq639
  have eq4297 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op (M.op X1 (M.op x y)) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq4245 X0 X1 x x
       have i₂ := eq14 y x x
       grind)
    | exact superpose eq14 eq4245
    | exact resolve eq4245 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4245
  have eq4844 : ∀ X0 : G, (σ (k X0 x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ x) = (k (σ X0) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq163 eq12
    | (have j0 := eq12 (σ X0) (σ x)
       have j1 := eq163 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq163 x
       grind)
    | (have r₁ := eq12 (σ X0) (σ x)
       have r₂ := eq163 X0
       grind)
    | exact resolve eq12 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq4868 : ∀ X0 : G, (σ (k X0 x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ x) = (k (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4844 X0
       have j1 := eq12 (σ X0) (σ x)
       grind)
    | (have r₁ := eq4844 x
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq4844 X0
       have r₂ := eq12 (σ X0) (σ x)
       grind)
    | exact resolve eq4844 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4844
  have eq4890 : ∀ X0 : G, (σ x) = (σ (k X0 x)) ∨ (σ (k X0 x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq39 eq4868
    | (have j0 := eq4868 X0
       grind)
    | exact resolve eq4868 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq4868
  have eq4891 : ∀ X0 : G, (σ (k X0 x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4890 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4890
  have eq7448 : ∀ X0 : G, (σ (k X0 (M.op x y))) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq773
    | (have j0 := eq773 (M.op x y) X0
       grind)
    | exact resolve eq773 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12299
    | exact resolve eq12299 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12299
  have eq12311 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12300
       have r₂ := eq27
       grind)
    | exact resolve eq12300 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12300
  have eq12316 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12311
    | exact resolve eq12311 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12311
  have eq12318 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12316
    | exact resolve eq12316 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12316
  have eq12615 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12318 eq77
    | (have r₁ := eq77
       have r₂ := eq12318
       grind)
    | exact resolve eq77 eq12318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12318
  have eq12653 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq12615
  have eq12654 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq12653
  have eq13650 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12654 eq83
    | exact resolve eq83 eq12654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq12654
  have eq13671 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq13650
    | exact resolve eq13650 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13650
  have eq13679 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13671
       have r₂ := eq76
       grind)
    | exact resolve eq13671 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13671
  have eq13682 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq13679
       grind)
    | exact superpose eq13679 eq73
    | exact resolve eq73 eq13679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13689 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq13679
       grind)
    | exact superpose eq13679 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq13679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13679
  have eq13690 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13689
  have eq13692 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13690
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13690
    | exact resolve eq13690 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13690
  have eq13693 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13692
  have eq13700 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13682
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13682
    | exact resolve eq13682 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13682
  have eq13703 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13693
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13693
    | exact resolve eq13693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13693
  have eq13719 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13700 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq13700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13700
  have eq13720 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13719
  have eq13724 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13720
    | exact resolve eq13720 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13720
  have eq13725 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13724
  have eq13737 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13725
    | exact resolve eq13725 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13725
  have eq13855 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3765 x
       have i₂ := eq13703
       grind)
    | exact superpose eq13703 eq3765
    | exact resolve eq3765 eq13703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13856 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3596 x
       have i₂ := eq13703
       grind)
    | exact superpose eq13703 eq3596
    | exact resolve eq3596 eq13703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13703
  have eq13901 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13737 eq3596
    | exact resolve eq3596 eq13737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14061 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13855 eq125
    | exact resolve eq125 eq13855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13855
  have eq14075 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14061
    | exact resolve eq14061 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14061
  have eq14194 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13856 eq685
    | exact resolve eq685 eq13856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq13856
  have eq14225 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14194
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14194
    | exact resolve eq14194 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14194
  have eq14385 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13901 eq692
    | exact resolve eq692 eq13901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq13901
  have eq14416 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14385
    | exact resolve eq14385 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14385
  have eq14541 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14225 eq66
    | exact resolve eq66 eq14225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14559 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14225 eq661
    | exact resolve eq661 eq14225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14564 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq204 eq14559
    | exact resolve eq14559 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14559
  have eq14581 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq204 eq14541
    | exact resolve eq14541 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14541
  have eq14658 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14416 eq661
    | exact resolve eq661 eq14416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14663 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq209 eq14658
    | exact resolve eq14658 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq14658
  have eq15105 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14564 eq14
    | exact resolve eq14 eq14564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14564
  have eq15284 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14663 eq14
    | exact resolve eq14 eq14663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14663
  have eq15699 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14225 eq15105
    | exact resolve eq15105 eq14225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14225 eq15105
  have eq15777 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15699 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15699
  have eq15801 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4⟩ := hcon
    have f15801_16 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f15801_17 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f15801_26 : (M.op x y) ≠ (k X0 (M.op x y)) := by grind
    have f15801_29 : x ≠ (M.op x y) := by grind
    have f15801_30 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f15801_31 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f15801_17 X0
         grind)
      | (have r₁ := f15801_17 X0
         have r₂ := f15801_29
         grind)
      | exact resolve f15801_17 f15801_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15801_32 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f15801_16 X0
         grind)
      | (have r₁ := f15801_16 X0
         have r₂ := f15801_29
         grind)
      | exact resolve f15801_16 f15801_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15801_33 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 := by
      intro X0
      first
      | (have j0 := f15801_31 X0
         grind)
      | (have r₁ := f15801_31 X0
         have r₂ := f15801_30
         grind)
      | exact resolve f15801_31 f15801_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15801_34 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) := by
      intro X0
      first
      | (have j0 := f15801_32 X0
         grind)
      | (have r₁ := f15801_32 X0
         have r₂ := f15801_30
         grind)
      | exact resolve f15801_32 f15801_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15801_35 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
      intro X0
      first
      | (have i₁ := f15801_34 X0
         have i₂ := f15801_33 X0
         grind)
      | exact superpose f15801_33 f15801_34
      | exact resolve f15801_34 f15801_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15801_36 : (M.op x y) ≠ (M.op x y) := by
      first
      | (have i₁ := f15801_26
         have i₂ := f15801_35 X0
         grind)
      | exact superpose f15801_35 f15801_26
      | (have r₁ := f15801_26
         have r₂ := f15801_35 X0
         grind)
      | exact resolve f15801_26 f15801_35
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15801_37 : False := by grind
    exact f15801_37
  clear eq14581 eq15777
  have eq15881 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15801 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15801
  have eq15942 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq15881 eq34
    | exact resolve eq34 eq15881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15881
  have eq15962 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq15942
    | (have j0 := eq15942 X0
       grind)
    | exact resolve eq15942 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15942
  have eq16138 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq15962
    | exact resolve eq15962 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16141 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15962 (M.op sF1 sF1)
       have i₂ := eq3765 sF1
       grind)
    | exact superpose eq3765 eq15962
    | exact resolve eq15962 eq3765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15962
  have eq16601 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16138 eq773
    | (have j0 := eq773 (M.op x y) X0
       grind)
    | exact resolve eq773 eq16138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq16138
  have eq16698 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq16601
    | (have j0 := eq16601 X0
       grind)
    | exact resolve eq16601 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16601
  have eq16709 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq16698 X0
       grind)
    | (have r₁ := eq16698 X0
       have r₂ := eq16141
       grind)
    | exact resolve eq16698 eq16141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16141 eq16698
  have eq16710 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq16709
    | (have j0 := eq16709 X0
       grind)
    | exact resolve eq16709 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16709
  have eq16711 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq16710
    | (have j0 := eq16710 X0
       grind)
    | exact resolve eq16710 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16710
  have eq16712 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq16711 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16711
  have eq16852 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16712 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq16712
    | exact resolve eq16712 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16712
  have eq17342 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14416 eq15284
    | exact resolve eq15284 eq14416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14416 eq15284
  have eq17420 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17342 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17342
  have eq17515 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f17515_15 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f17515_21 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
      intro X0 X1 X2
      grind
    have f17515_24 : (σ x) ≠ (M.op (σ x) (M.op X0 (σ y))) := by grind
    have f17515_25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f17515_26 : x ≠ (M.op x y) := by grind
    have f17515_27 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f17515_15 X0
         grind)
      | (have r₁ := f17515_15 X0
         have r₂ := f17515_25
         grind)
      | exact resolve f17515_15 f17515_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17515_28 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 := by
      intro X0
      first
      | (have j0 := f17515_27 X0
         grind)
      | (have r₁ := f17515_27 X0
         have r₂ := f17515_26
         grind)
      | exact resolve f17515_27 f17515_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17515_37 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ y))) := by
      intro X0
      first
      | (have i₁ := f17515_21 (σ x) X0 (σ y)
         have i₂ := f17515_28 X0
         grind)
      | exact superpose f17515_28 f17515_21
      | exact resolve f17515_21 f17515_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17515_163 : (σ x) ≠ (σ x) := by
      first
      | (have i₁ := f17515_24
         have i₂ := f17515_37 X0
         grind)
      | exact superpose f17515_37 f17515_24
      | (have r₁ := f17515_24
         have r₂ := f17515_37 X0
         grind)
      | exact resolve f17515_24 f17515_37
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17515_171 : False := by grind
    exact f17515_171
  clear eq51 eq17420
  have eq18774 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16852 eq17515
    | exact resolve eq17515 eq16852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16852 eq17515
  have eq18828 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18774
  have eq18873 : (M.op (σ x) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18828 eq658
    | exact resolve eq658 eq18828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18828
  have eq30887 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18873 eq14075
    | exact resolve eq14075 eq18873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14075 eq18873
  have eq30894 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30887
  have eq30902 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30894 eq13737
    | exact resolve eq13737 eq30894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13737 eq30894
  have eq30954 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30902
  have eq30958 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30954
       have r₂ := eq27
       grind)
    | exact resolve eq30954 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30954
  have eq31231 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30958 eq27
    | exact resolve eq27 eq30958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31246 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30958 eq697
    | exact resolve eq697 eq30958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq31262 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ y) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30958 eq3642
    | exact resolve eq3642 eq30958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3642
  have eq31311 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31246 eq109
    | exact resolve eq109 eq31246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq31315 : (k (k y x) x) = (τ (k (M.op (σ x) (σ x)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31246 eq490
    | exact resolve eq490 eq31246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq31246
  have eq31330 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq31311
  have eq31337 : (τ (M.op (σ x) (σ x))) = (k (k y x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31315
       have i₂ := eq3765 sF2
       grind)
    | exact superpose eq3765 eq31315
    | exact resolve eq31315 eq3765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31315
  have eq31649 : (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (σ y) (σ y))) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31262 eq661
    | exact resolve eq661 eq31262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31262
  have eq31691 : (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31649
       have i₂ := eq3596 sF3
       grind)
    | exact superpose eq3596 eq31649
    | exact resolve eq31649 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31649
  have eq32587 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31330 eq3765
    | exact resolve eq3765 eq31330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32932 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32587 eq136
    | exact resolve eq136 eq32587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq32587
  have eq32953 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq32932
    | exact resolve eq32932 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32932
  have eq108533 : (M.op (σ x) (σ x)) ≠ (σ (τ (M.op (σ x) (σ x)))) ∨ (σ x) = (σ (τ (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ (k y x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4891 (k y x)
       have i₂ := eq31337
       grind)
    | exact superpose eq31337 eq4891
    | (have j0 := eq4891 (k y x)
       grind)
    | exact resolve eq4891 eq31337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4891 eq31337
  have eq108623 : (σ x) = (σ (τ (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ (k y x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq108533
       have r₂ := eq15 (M.op (σ x) (σ x))
       grind)
    | exact resolve eq108533 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108533
  have eq108633 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (k y x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108623
       have i₂ := eq15 (M.op sF2 sF2)
       grind)
    | exact superpose eq15 eq108623
    | exact resolve eq108623 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108623
  have eq108641 : (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108633
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq108633
    | exact resolve eq108633 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108633
  have eq117848 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (M.op (σ y) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31691 eq661
    | exact resolve eq661 eq31691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31691
  have eq128383 : (σ x) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117848 eq14
    | exact resolve eq14 eq117848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117848
  have eq128505 : (σ x) = (M.op (σ x) (k (σ y) (M.op (σ y) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128383
       have i₂ := eq658 sF3 sF3
       grind)
    | exact superpose eq658 eq128383
    | exact resolve eq128383 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128383
  have eq128525 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128505
       have i₂ := eq3663 sF3
       grind)
    | exact superpose eq3663 eq128505
    | exact resolve eq128505 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128505
  have eq128547 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128525 eq3621
    | exact resolve eq3621 eq128525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621 eq128525
  have eq128688 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq128547
    | exact resolve eq128547 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128547
  have eq134386 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30958 eq128688
    | exact resolve eq128688 eq30958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30958 eq128688
  have eq134499 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq134386
  have eq139734 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq134499 eq658
    | exact resolve eq658 eq134499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134499
  have eq139803 : (k (σ x) (M.op (σ x) (σ x))) = (k (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139734
       have i₂ := eq658 sF2 sF2
       grind)
    | exact superpose eq658 eq139734
    | exact resolve eq139734 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139734
  have eq139814 : (M.op (σ x) (σ x)) = (k (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139803
       have i₂ := eq3663 sF2
       grind)
    | exact superpose eq3663 eq139803
    | exact resolve eq139803 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139803
  have eq146086 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31330 eq139814
    | exact resolve eq139814 eq31330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31330 eq139814
  have eq146098 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq146086
  have eq147945 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq146098 eq93
    | exact resolve eq93 eq146098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq146098
  have eq147998 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq690 eq147945
    | exact resolve eq147945 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq147945
  have eq148000 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq30 eq147998
    | exact resolve eq147998 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq147998
  have eq148062 : x = (M.op x (M.op (M.op x y) y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq148000 eq50
    | exact resolve eq50 eq148000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq148000
  have eq148322 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq667 eq148062
    | exact resolve eq148062 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq148062
  have eq148406 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3596 x
       have i₂ := eq148322
       grind)
    | exact superpose eq148322 eq3596
    | exact resolve eq3596 eq148322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596 eq148322
  have eq148488 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq148406
  have eq148507 : (M.op x x) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148488 eq439
    | exact resolve eq439 eq148488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq148530 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148488 eq3628
    | exact resolve eq3628 eq148488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3628
  have eq148537 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq148488 eq4297
    | exact resolve eq4297 eq148488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4297 eq148488
  have eq148636 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq148537 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq148537
    | (have j0 := eq148537 X0
       grind)
    | exact resolve eq148537 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148537
  have eq148639 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq148530
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq148530
    | exact resolve eq148530 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq148530
  have eq148659 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq204 eq148636
    | exact resolve eq148636 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148636
  have eq148853 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq148639 eq66
    | exact resolve eq66 eq148639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148986 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq204 eq148853
    | exact resolve eq148853 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq148853
  have eq149195 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148507 eq32953
    | exact resolve eq32953 eq148507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32953 eq148507
  have eq149220 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq149195
  have eq149240 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq149220
       grind)
    | exact superpose eq149220 eq76
    | (have r₁ := eq76
       have r₂ := eq149220
       grind)
    | exact resolve eq76 eq149220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq149260 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3765 x
       have i₂ := eq149220
       grind)
    | exact superpose eq149220 eq3765
    | exact resolve eq3765 eq149220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149220
  have eq149342 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq149240
  have eq149343 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq149342
  have eq149449 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq149260 eq125
    | exact resolve eq125 eq149260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq149260
  have eq149517 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq149449
    | exact resolve eq149449 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149449
  have eq149529 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq149343
       grind)
    | exact superpose eq149343 eq73
    | exact resolve eq73 eq149343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq149343
  have eq149599 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq149529
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq149529
    | exact resolve eq149529 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149529
  have eq152606 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq149599 eq108641
    | exact resolve eq108641 eq149599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108641 eq149599
  have eq152626 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq152606
  have eq152784 : ∀ X0 : G, (σ x) = (k (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq152626 eq66
    | exact resolve eq66 eq152626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152626
  have eq152990 : ∀ X0 : G, (σ x) = (k (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq152784 x
       have i₂ := eq657 sF2 x
       grind)
    | exact superpose eq657 eq152784
    | exact resolve eq152784 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152784
  have eq158284 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq148659 eq14
    | exact resolve eq14 eq148659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148659
  have eq160289 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq148639 eq158284
    | exact resolve eq158284 eq148639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148639 eq158284
  have eq160581 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq160289 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160289
  have eq160749 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq160581 eq148986
    | exact resolve eq148986 eq160581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148986 eq160581
  have eq161044 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq160749 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160749
  have eq161293 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq161044 eq34
    | exact resolve eq34 eq161044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161044
  have eq161486 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq161293
    | (have j0 := eq161293 X0
       grind)
    | exact resolve eq161293 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161293
  have eq162221 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq161486
    | exact resolve eq161486 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq162235 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq161486 (M.op sF1 sF1)
       have i₂ := eq3765 sF1
       grind)
    | exact superpose eq3765 eq161486
    | exact resolve eq161486 eq3765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3765 eq161486
  have eq169721 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq162221 eq7448
    | (have j0 := eq7448 X0
       grind)
    | exact resolve eq7448 eq162221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7448 eq162221
  have eq169899 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq169721 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169721
  have eq169943 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq169899 X0
       grind)
    | (have r₁ := eq169899 X0
       have r₂ := eq162235
       grind)
    | exact resolve eq169899 eq162235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162235 eq169899
  have eq174085 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq169943 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq169943
    | exact resolve eq169943 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169943
  have eq185821 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq174085 eq152990
    | exact resolve eq152990 eq174085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152990 eq174085
  have eq185882 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq185821
  have eq185945 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq185882 eq149517
    | exact resolve eq149517 eq185882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149517 eq185882
  have eq185951 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq185945
  have eq185973 : x = (M.op x y) := by
    first
    | (have r₁ := eq185951
       have r₂ := eq31231
       grind)
    | exact resolve eq185951 eq31231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31231 eq185951
  have eq185991 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq185973 eq20
    | exact resolve eq20 eq185973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq186049 : (k (σ y) (σ (M.op x y))) = (σ (M.op x x)) := by
    first
    | exact superpose eq185973 eq699
    | exact resolve eq699 eq185973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq186307 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq185991
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq185991
    | exact resolve eq185991 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq185991
  have eq186347 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq186307 eq26
    | exact resolve eq26 eq186307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq186359 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq186307 eq77
    | exact resolve eq77 eq186307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq186307
  have eq186741 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq186359
       have r₂ := eq27
       grind)
    | exact resolve eq186359 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186359
  have eq270213 : ∀ X0 X1 X2 X3 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op (M.op X1 (M.op X0 x)) (M.op (k x (M.op X0 x)) (M.op (M.op X2 (M.op (M.op X0 x) X3)) X3)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq185973 eq4157
    | exact resolve eq4157 eq185973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4157 eq185973
  have eq270237 : ∀ X0 X1 X2 : G, (M.op x x) = (M.op (M.op x x) (M.op (M.op X0 (M.op x x)) (M.op (M.op x x) (M.op (M.op X1 (M.op (M.op x x) X2)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq270213 x X0 X1 X2
       have i₂ := eq3663 x
       grind)
    | exact superpose eq3663 eq270213
    | exact resolve eq270213 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270213
  have eq270642 : ∀ X0 : G, (M.op x x) = (M.op (M.op x x) (M.op (M.op X0 (M.op x x)) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq270237 X0 x x
       have i₂ := eq14 (M.op x x) x x
       grind)
    | exact superpose eq14 eq270237
    | exact resolve eq270237 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270237
  have eq270665 : ∀ X0 : G, (M.op x x) = (M.op (M.op x x) (M.op X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq270642 X0
       have i₂ := eq657 (M.op x x) X0
       grind)
    | exact superpose eq657 eq270642
    | exact resolve eq270642 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq270642
  have eq291768 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x x) (M.op x x)
       have i₂ := eq270665 X0
       grind)
    | exact superpose eq270665 eq14
    | exact resolve eq14 eq270665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291770 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op x x) (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq66 X0 (M.op x x) (M.op x x)
       have i₂ := eq270665 X0
       grind)
    | exact superpose eq270665 eq66
    | exact resolve eq66 eq270665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270665
  have eq292025 : ∀ X0 : G, (M.op X0 X0) = (k (k x (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq291770 X0
       have i₂ := eq658 x x
       grind)
    | exact superpose eq658 eq291770
    | exact resolve eq291770 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291770
  have eq292027 : ∀ X0 : G, (M.op X0 (k x (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq291768 X0
       have i₂ := eq658 x x
       grind)
    | exact superpose eq658 eq291768
    | exact resolve eq291768 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq291768
  have eq292134 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq292025 X0
       have i₂ := eq3663 x
       grind)
    | exact superpose eq3663 eq292025
    | exact resolve eq292025 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292025
  have eq292136 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq292027 X0
       have i₂ := eq3663 x
       grind)
    | exact superpose eq3663 eq292027
    | exact resolve eq292027 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292027
  have eq293738 : ∀ X0 : G, (k x (M.op x x)) = (k (M.op X0 (k x (M.op x x))) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq1377 x x X0
       have i₂ := eq292136 (M.op X0 (k x (M.op x x)))
       grind)
    | exact superpose eq292136 eq1377
    | exact resolve eq1377 eq292136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq293802 : ∀ X0 X1 : G, (M.op X1 (M.op x x)) = (M.op (M.op X1 (M.op x x)) (M.op X0 (M.op X1 (M.op x x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq661 (M.op x x) X1 X0
       have i₂ := eq292136 (M.op X0 (M.op X1 (M.op x x)))
       grind)
    | exact superpose eq292136 eq661
    | exact resolve eq661 eq292136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq294044 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq293802 X0 X0
       have i₂ := eq292136 X0
       grind)
    | exact superpose eq292136 eq293802
    | exact resolve eq293802 eq292136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293802
  have eq294106 : ∀ X0 : G, (M.op x x) = (k (M.op X0 (M.op x x)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq293738 X0
       have i₂ := eq3663 x
       grind)
    | exact superpose eq3663 eq293738
    | exact resolve eq293738 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663 eq293738
  have eq294265 : ∀ X0 : G, (M.op x x) = (k X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq294106 X0
       have i₂ := eq292136 X0
       grind)
    | exact superpose eq292136 eq294106
    | exact resolve eq294106 eq292136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292136 eq294106
  have eq295926 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq294044 X1 X0
       grind)
    | exact superpose eq294044 eq14
    | exact resolve eq14 eq294044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295928 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X1 X0 X0
       have i₂ := eq294044 X1 X0
       grind)
    | exact superpose eq294044 eq66
    | exact resolve eq66 eq294044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq294044
  have eq299922 : ∀ X0 X1 : G, (M.op X1 (k (M.op x x) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq295926 X0 X1
       have i₂ := eq292134 X0
       grind)
    | exact superpose eq292134 eq295926
    | exact resolve eq295926 eq292134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292134 eq295926
  have eq310019 : ∀ X0 : G, (σ (M.op x x)) = (k X0 (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op x x)
       have i₂ := eq294265 (τ X0)
       grind)
    | exact superpose eq294265 eq34
    | exact resolve eq34 eq294265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq294265
  have eq310267 : ∀ X0 : G, (k (σ y) (σ (M.op x y))) = (k X0 (k (σ y) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq310019 X0
       have i₂ := eq186049
       grind)
    | exact superpose eq186049 eq310019
    | exact resolve eq310019 eq186049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186049 eq310019
  have eq345249 : ∀ X0 : G, (M.op X0 (k (σ y) (σ (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq310267 eq299922
    | exact resolve eq299922 eq310267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299922 eq310267
  have eq346075 : ∀ X0 : G, (M.op X0 X0) = (k (k (σ y) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq345249 eq295928
    | exact resolve eq295928 eq345249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295928 eq345249
  have eq350850 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3855 eq346075
    | exact resolve eq346075 eq3855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3855 eq346075
  have eq352406 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq350850 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq350850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352407 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq352406
  have eq352411 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq186347 eq352407
    | exact resolve eq352407 eq186347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352407
  have eq352422 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq186347 eq352411
    | exact resolve eq352411 eq186347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186347 eq352411
  have eq352431 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq352422
       have r₂ := eq27
       grind)
    | exact resolve eq352422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352422
  have eq352459 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq352431 eq186741
    | (have r₁ := eq186741
       have r₂ := eq352431
       grind)
    | exact resolve eq186741 eq352431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186741
  have eq352625 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by grind
  clear eq352459
  have eq352661 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq350850 eq352625
    | exact resolve eq352625 eq350850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350850 eq352625
  have eq352664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq352431 eq352661
    | exact resolve eq352661 eq352431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352431 eq352661
  have eq352665 : False := by grind
  exact eq352665

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pyx_pyx_pxx_pyx_Equation1445 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1445 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq267 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq81 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq280 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq281 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq280 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq286 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       have j1 := eq277 X1 X0
       grind)
    | (have r₁ := eq283 X1 X0
       have r₂ := eq277 X0 X1
       grind)
    | (have r₁ := eq283 X1 (k X1 X0)
       have r₂ := eq277 X0 X1
       grind)
    | (have r₁ := eq283 X1 X1
       have r₂ := eq277 X1 X1
       grind)
    | exact resolve eq283 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq283
  have eq528 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq286 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq286
    | exact resolve eq286 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq286 y x
       grind)
    | exact superpose eq286 eq16
    | (have j1 := eq286 y x
       grind)
    | exact resolve eq16 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq551 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq528
    | (have j0 := eq528 X0 X1
       grind)
    | exact resolve eq528 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq528
  have eq553 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq551
    | exact resolve eq551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq601 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq553 (τ X0) X1
       grind)
    | exact superpose eq553 eq19
    | (have j1 := eq553 (τ X0) X1
       grind)
    | exact resolve eq19 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq553
  have eq850 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq601 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq601
    | exact resolve eq601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq904 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq850 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq850
    | (have j0 := eq850 X0 X1
       grind)
    | exact resolve eq850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq969 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq536
       have i₂ := eq904 x y
       grind)
    | exact superpose eq904 eq536
    | (have j1 := eq904 (σ x) (σ y)
       grind)
    | (have r₁ := eq536
       have r₂ := eq904 x y
       grind)
    | exact resolve eq536 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq969
  have eq977 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq970
  have eq1024 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq536
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq536
    | exact resolve eq536 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq977
  have eq1025 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1024
  have eq1026 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1025
  have eq1040 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1026
  have eq1047 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1040
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1040
    | exact resolve eq1040 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1088 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq16
    | exact resolve eq16 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1098 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1088
       have i₂ := eq904 x y
       grind)
    | exact superpose eq904 eq1088
    | (have j1 := eq904 x y
       grind)
    | (have r₁ := eq1088
       have r₂ := eq904 x y
       grind)
    | exact resolve eq1088 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq1099 : x = (M.op y y) := by grind
  clear eq1098
  have eq1113 : (M.op x y) = (k y x) := by grind
  clear eq1099
  have eq1122 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1088
       have i₂ := eq1113
       grind)
    | exact superpose eq1113 eq1088
    | exact resolve eq1088 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088 eq1113
  have eq1125 : False := by grind
  exact eq1125

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_y_pyx_y_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq79 : x ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) := by
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
  have eq80 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq95 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq109 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq87 y x
       grind)
    | exact superpose eq87 eq93
    | (have j1 := eq87 y x
       grind)
    | exact resolve eq93 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq125
    | exact resolve eq125 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq128 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq127
    | exact resolve eq127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq191 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq87 (σ X0) sF2
       grind)
    | exact superpose eq87 eq39
    | (have j1 := eq87 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq87
    | (have j0 := eq87 (σ y) (σ x)
       grind)
    | exact resolve eq87 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq197
    | exact resolve eq197 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq201 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq198
       have r₂ := eq27
       grind)
    | exact resolve eq198 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq203 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq201
    | exact resolve eq201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq205 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203 eq27
    | exact resolve eq27 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203 eq80
    | (have r₁ := eq80
       have r₂ := eq203
       grind)
    | exact resolve eq80 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq203
  have eq475 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq474
  have eq479 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq475 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq475
       grind)
    | exact resolve eq13 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq2418 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq479 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq2423 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2418
    | exact resolve eq2418 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq2425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq2423
    | exact resolve eq2423 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq2423
  have eq2433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2425
  have eq2436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2433
       have r₂ := eq205
       grind)
    | exact resolve eq2433 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq2433
  have eq2437 : x = (M.op x y) := by
    first
    | (have r₁ := eq2436
       have r₂ := eq27
       grind)
    | exact resolve eq2436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436
  have eq2438 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2437 eq20
    | exact resolve eq20 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2441 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) := by
    first
    | exact superpose eq2437 eq79
    | (have r₁ := eq79
       have r₂ := eq2437
       grind)
    | exact resolve eq79 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2448 : (M.op y x) = (M.op y y) ∨ x = (k y x) := by grind
  clear eq2441
  have eq2456 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2438
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2438
    | exact resolve eq2438 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2438
  have eq2528 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2456 eq26
    | exact resolve eq26 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2829 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq2448
       grind)
    | exact superpose eq2448 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2448
       grind)
    | exact resolve eq13 eq2448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq3138 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2456 eq191
    | (have j0 := eq191 X0
       grind)
    | exact resolve eq191 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq3139 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2456 eq3138
    | (have j0 := eq3138 X0
       grind)
    | exact resolve eq3138 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3138
  have eq3267 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq3139 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3139
    | (have j0 := eq3139 y
       grind)
    | exact resolve eq3139 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3139
  have eq3280 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2528 eq3267
    | exact resolve eq3267 eq2528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3267
  have eq3302 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq3280
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq3280
    | exact resolve eq3280 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq3280
  have eq3317 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2456 eq3302
    | exact resolve eq3302 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3302
  have eq3326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2528 eq3317
    | exact resolve eq3317 eq2528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528 eq3317
  have eq3331 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3326
       have r₂ := eq27
       grind)
    | exact resolve eq3326 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326
  have eq3339 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3331 eq109
    | exact resolve eq109 eq3331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq3331
  have eq3341 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2437 eq3339
    | exact resolve eq3339 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3339
  have eq789958 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2829 X0
       have i₂ := eq3341
       grind)
    | exact superpose eq3341 eq2829
    | (have j0 := eq2829 X0
       grind)
    | exact resolve eq2829 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829
  have eq789973 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y x) := by
    first
    | (have j0 := eq789958 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789958
  have eq789977 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq789973
       have i₂ := eq3341
       grind)
    | exact superpose eq3341 eq789973
    | exact resolve eq789973 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341 eq789973
  have eq789980 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq789977
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq789977
    | exact resolve eq789977 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq789977
  have eq789981 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2437 eq789980
    | exact resolve eq789980 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2437 eq789980
  have eq789982 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq789981
  have eq790078 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq789982 eq15
    | exact resolve eq15 eq789982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789982
  have eq790730 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq790078
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq790078
    | exact resolve eq790078 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq790078
  have eq790824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2456 eq790730
    | exact resolve eq790730 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2456 eq790730
  have eq790840 : False := by grind
  exact eq790840

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pxy_pyx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq40 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq36 (τ X0)
       grind)
    | exact superpose eq36 eq18
    | exact resolve eq18 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
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
  clear eq38
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq41
    | exact resolve eq41 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq41
  have eq83 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq93
  have eq561 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq95 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq570 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq561 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq574 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq570 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq570 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq570 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq570 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq574
    | (have j0 := eq574 X0 X1
       grind)
    | exact resolve eq574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq591 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq590 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq1641 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq591 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq591
    | (have j0 := eq591 (τ X0) X1
       grind)
    | exact resolve eq591 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq1676 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1641 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1641
    | (have j0 := eq1641 X0 X1
       grind)
    | exact resolve eq1641 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1641
  have eq1684 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1676 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq1676
    | (have j0 := eq1676 X0 X1
       grind)
    | exact resolve eq1676 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1676
  have eq1690 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1684 X0 X1
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq1684 X1 X0
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq1684 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1684
  have eq1695 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1690 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1690
    | exact resolve eq1690 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1702 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1690 (σ X1) X0
       grind)
    | exact superpose eq1690 eq15
    | exact resolve eq15 eq1690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq2006 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1702 x y
       grind)
    | exact superpose eq1702 eq16
    | exact resolve eq16 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702
  have eq2097 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2006
       have i₂ := eq1695 x y
       grind)
    | exact superpose eq1695 eq2006
    | exact resolve eq2006 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695 eq2006
  have eq2098 : False := by grind
  exact eq2098

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq84 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq283 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq81 X0 X0
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq81 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq81 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq287 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq286 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq289 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq294 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq289 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq289 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq303 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq287 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq287
    | (have j0 := eq287 (τ X0)
       grind)
    | exact resolve eq287 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq287
  have eq305 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq303 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq303
    | (have j0 := eq303 X0
       grind)
    | exact resolve eq303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq308 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq305 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq305
    | (have j0 := eq305 X0
       grind)
    | exact resolve eq305 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq314 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq308 (τ X0)
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq308
    | (have j0 := eq308 (τ X0)
       grind)
    | exact resolve eq308 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq490 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq524 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq490 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq490
    | (have j0 := eq490 X0 X1
       grind)
    | exact resolve eq490 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq3462 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq82 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq3463 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462
  have eq3471 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3463 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3463
    | (have j0 := eq3463 X0
       grind)
    | exact resolve eq3463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3463
  have eq3476 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3471 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3471
    | exact resolve eq3471 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471
  have eq3519 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3476 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq3476
    | (have j0 := eq3476 X0
       grind)
    | exact resolve eq3476 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq3525 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3519 X0
       grind)
    | exact superpose eq3519 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq3519 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3519 X0
       grind)
    | exact resolve eq12 eq3519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3519
  have eq3566 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3525 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3525
  have eq3611 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3566 X0 X1
       grind)
    | exact superpose eq3566 eq11
    | (have j1 := eq3566 X0 X1
       grind)
    | exact resolve eq11 eq3566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq3719 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3611 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3611
    | (have j0 := eq3611 X0 X0
       grind)
    | exact resolve eq3611 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3611
  have eq3806 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3719 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719
  have eq3807 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3806 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq3955 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq3807 X0
       grind)
    | exact superpose eq3807 eq294
    | (have j0 := eq294 X0 X1
       grind)
    | exact resolve eq294 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq3958 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq314 X0
       have i₂ := eq3807 X0
       grind)
    | exact superpose eq3807 eq314
    | (have j0 := eq314 X0
       grind)
    | exact resolve eq314 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq3993 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3807 (σ X0)
       grind)
    | exact superpose eq3807 eq15
    | exact resolve eq15 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4000 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq3807 (τ X0)
       grind)
    | exact superpose eq3807 eq35
    | exact resolve eq35 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq4051 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4000 X0
       have i₂ := eq3807 X0
       grind)
    | exact superpose eq3807 eq4000
    | exact resolve eq4000 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4000
  have eq4057 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3993 X0
       have i₂ := eq3807 X0
       grind)
    | exact superpose eq3807 eq3993
    | exact resolve eq3993 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3807 eq3993
  have eq6192 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3958 (σ X0)
       have i₂ := eq88 X1 X0
       grind)
    | exact superpose eq88 eq3958
    | (have j0 := eq3958 (σ X0)
       have j1 := eq88 X1 X0
       grind)
    | exact resolve eq3958 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq3958
  have eq6211 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq6192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6192
  have eq6223 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6211 X0 X1
       have i₂ := eq4051 (σ X0)
       grind)
    | exact superpose eq4051 eq6211
    | (have j0 := eq6211 X0 X1
       grind)
    | exact resolve eq6211 eq4051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4051 eq6211
  have eq6244 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6223 X0 X1
       have i₂ := eq4057 X0
       grind)
    | exact superpose eq4057 eq6223
    | (have j0 := eq6223 X0 X1
       grind)
    | exact resolve eq6223 eq4057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6223
  have eq6263 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6244 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6244
    | (have j0 := eq6244 X0 X1
       grind)
    | exact resolve eq6244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6244
  have eq6280 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6263 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6263
    | (have j0 := eq6263 X0 X1
       grind)
    | exact resolve eq6263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6263
  have eq73182 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq6280 X1 X0
       grind)
    | exact superpose eq6280 eq11
    | (have j1 := eq6280 X1 X0
       grind)
    | exact resolve eq11 eq6280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6280
  have eq73332 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73182 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq73182
    | (have j0 := eq73182 X0 X1
       grind)
    | exact resolve eq73182 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq73182
  have eq73643 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq73332 (σ X0) X1
       grind)
    | exact superpose eq73332 eq15
    | (have j1 := eq73332 (σ X0) X1
       grind)
    | exact resolve eq15 eq73332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73332
  have eq114440 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73643 x y
       grind)
    | exact superpose eq73643 eq16
    | (have j1 := eq73643 x y
       grind)
    | exact resolve eq16 eq73643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114842 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq73643 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73643
  have eq117514 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq114440
       have i₂ := eq524 x y
       grind)
    | exact superpose eq524 eq114440
    | (have j1 := eq524 y y
       grind)
    | (have r₁ := eq114440
       have r₂ := eq524 x y
       grind)
    | exact resolve eq114440 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114440
  have eq117515 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq117514
  have eq117516 : y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq117515
  have eq117885 : y ≠ y ∨ y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq117516
       grind)
    | exact superpose eq117516 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq117516
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq117516
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq117516
       grind)
    | exact resolve eq13 eq117516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117516
  have eq117911 : y ≠ y ∨ y = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq117885
  have eq117912 : y = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq117911
  have eq117955 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq114842 x y
       have i₂ := eq117912
       grind)
    | exact superpose eq117912 eq114842
    | (have j0 := eq114842 x y
       grind)
    | exact resolve eq114842 eq117912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114842 eq117912
  have eq117958 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq117955
  have eq117959 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq117958
  have eq118160 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq117959
       grind)
    | exact superpose eq117959 eq16
    | exact resolve eq16 eq117959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118176 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq117959
       grind)
    | exact superpose eq117959 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq117959
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq117959
       grind)
    | exact resolve eq13 eq117959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117959
  have eq118202 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq118176
  have eq118207 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq118202
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq118202
    | exact resolve eq118202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118202
  have eq118215 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq118207
       have i₂ := eq4057 y
       grind)
    | exact superpose eq4057 eq118207
    | exact resolve eq118207 eq4057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4057 eq118207
  have eq119934 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq524 x y
       have i₂ := eq118215
       grind)
    | exact superpose eq118215 eq524
    | (have j0 := eq524 x y
       grind)
    | exact resolve eq524 eq118215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq118215
  have eq120101 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq119934
  have eq120177 : y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq120101
       have r₂ := eq118160
       grind)
    | exact resolve eq120101 eq118160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120101
  have eq120754 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq118160
       have i₂ := eq120177
       grind)
    | exact superpose eq120177 eq118160
    | exact resolve eq118160 eq120177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118160 eq120177
  have eq120784 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq120754
  have eq120785 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq120784
  have eq121373 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq120785
       grind)
    | exact superpose eq120785 eq10
    | exact resolve eq10 eq120785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120785
  have eq121602 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq121373
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq121373
    | exact resolve eq121373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121373
  have eq121603 : y = (M.op y y) := by grind
  clear eq121602
  have eq121616 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq121603
       grind)
    | exact superpose eq121603 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq121603
       grind)
    | exact resolve eq12 eq121603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121667 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3955 y X0
       have i₂ := eq121603
       grind)
    | exact superpose eq121603 eq3955
    | (have j0 := eq3955 y X0
       grind)
    | exact resolve eq3955 eq121603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3955 eq121603
  have eq121949 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq121667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121667
  have eq121954 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq121616 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121616
  have eq125044 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq121949 (σ X0)
       grind)
    | exact superpose eq121949 eq15
    | exact resolve eq15 eq121949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121949
  have eq125165 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq125044 X0
       have i₂ := eq121954 X0
       grind)
    | exact superpose eq121954 eq125044
    | exact resolve eq125044 eq121954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121954 eq125044
  have eq135326 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq125165 x
       grind)
    | exact superpose eq125165 eq16
    | (have r₁ := eq16
       have r₂ := eq125165 x
       grind)
    | exact resolve eq16 eq125165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125165
  have eq135697 : False := by grind
  exact eq135697

/-- `Equation1543`: `x = (y ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pxy_pxx_pxy_Equation1543 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1543 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1543.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X2 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X2)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) X2 (M.op X1 X1)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X2 X1
       have i₂ := eq77 X0 X1
       grind)
    | (have i₁ := eq77 X0 X1
       have i₂ := eq77 X1 X1
       grind)
    | exact superpose eq77 eq77
    | (have j0 := eq77 X2 X1
       have j1 := eq77 X2 X1
       grind)
    | exact resolve eq77 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X3))) = X3 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X2
       have i₂ := eq77 X0 X1
       grind)
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq77 X1 X1
       grind)
    | exact superpose eq77 eq14
    | (have j1 := eq77 X0 X1
       grind)
    | exact resolve eq14 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X1 (M.op X0 X1))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 X1
       have i₂ := eq77 X0 X1
       grind)
    | (have i₁ := eq14 X1 X1 X0
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq14
    | (have j1 := eq77 X0 X1
       grind)
    | exact resolve eq14 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq105 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq103
    | exact resolve eq103 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq107 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq105
    | exact resolve eq105 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq119 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X2) = (M.op X2 X1) ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq77 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq77 X1 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq77 X1 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (M.op X0 y)) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq107
       have i₂ := eq77 X0 y
       grind)
    | (have i₁ := eq107
       have i₂ := eq77 y y
       grind)
    | exact superpose eq77 eq107
    | (have j1 := eq77 X0 y
       grind)
    | exact resolve eq107 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq107
  have eq331 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq34
    | exact resolve eq34 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq331 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq331
    | exact resolve eq331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq343 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq341 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq341
    | exact resolve eq341 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq479 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq14
    | exact resolve eq14 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq516 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op X2 (M.op X2 X0)) X3 x X1
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 x x X0
       have i₂ := eq52 X1 x x X2
       grind)
    | (have i₁ := eq52 X0 X1 X1 x
       have i₂ := eq52 X0 X1 X2 (M.op X1 X1)
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X2 X2) X0) x X2 X1
       have i₂ := eq14 X0 x (M.op X2 X2)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have i₂ := eq52 (M.op X1 X1) (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq733 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq343 X0
       grind)
    | exact superpose eq343 eq16
    | exact resolve eq16 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq810 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 X1))) = X1 ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq86
    | (have j0 := eq86 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq86 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq901 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq88
    | (have j0 := eq88 (σ x) (σ y) X0
       grind)
    | exact resolve eq88 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1015 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (τ X0) X1
       have i₂ := eq733 X0
       grind)
    | exact superpose eq733 eq14
    | exact resolve eq14 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : ∀ X0 : G, y = (M.op (τ (M.op X0 X0)) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq733 X0
       grind)
    | exact superpose eq733 eq50
    | exact resolve eq50 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq733
  have eq1184 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq658
    | (have j0 := eq658 (σ x) (σ y) X0
       grind)
    | exact resolve eq658 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1892 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1893 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1892 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq1892 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq1892 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq1892 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892
  have eq5250 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1893 x y
       grind)
    | exact superpose eq1893 eq44
    | (have j1 := eq1893 x y
       grind)
    | exact resolve eq44 eq1893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5300 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1893 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5312 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq5250
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5250
    | exact resolve eq5250 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5250
  have eq5353 : (k x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5312
    | exact resolve eq5312 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5312
  have eq5856 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq5353
       grind)
    | exact superpose eq5353 eq44
    | exact resolve eq44 eq5353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5353
  have eq5871 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq5856
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq5856
    | exact resolve eq5856 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq5856
  have eq13844 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5871
       have i₂ := eq1893 sF2 sF3
       grind)
    | exact superpose eq1893 eq5871
    | (have j1 := eq1893 (σ x) (σ y)
       grind)
    | exact resolve eq5871 eq1893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq13845 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5871
       have i₂ := eq83 X0 sF3 sF2
       grind)
    | exact superpose eq83 eq5871
    | (have j1 := eq83 (σ x) (σ y) X0
       grind)
    | exact resolve eq5871 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq5871
  have eq13863 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq13845
    | (have j0 := eq13845 X0
       grind)
    | exact resolve eq13845 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13845
  have eq13864 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13844
    | exact resolve eq13844 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13844
  have eq13866 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq13863
    | (have j0 := eq13863 X0
       grind)
    | exact resolve eq13863 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13863
  have eq13867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13864
    | exact resolve eq13864 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13864
  have eq13868 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq13866 X0
       grind)
    | (have r₁ := eq13866 X0
       have r₂ := eq27
       grind)
    | exact resolve eq13866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13866
  have eq13869 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq13867
       have r₂ := eq27
       grind)
    | exact resolve eq13867 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13867
  have eq13870 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq13868
    | (have j0 := eq13868 X0
       grind)
    | exact resolve eq13868 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13868
  have eq17112 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq13870
    | (have j0 := eq13870 (σ X0)
       grind)
    | exact resolve eq13870 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq13870
  have eq17861 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq17112 eq1184
    | (have j1 := eq17112 X0
       grind)
    | exact resolve eq1184 eq17112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17112
  have eq20848 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (σ (k (τ X0) y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17861 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq17861
    | exact resolve eq17861 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17861
  have eq21060 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20848 X0
       have i₂ := eq34 X0 y
       grind)
    | exact superpose eq34 eq20848
    | (have j0 := eq20848 X0
       grind)
    | exact resolve eq20848 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq20848
  have eq21094 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq21060 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21060
    | (have j0 := eq21060 X0
       grind)
    | exact resolve eq21060 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21060
  have eq21295 : ∀ X0 : G, (k X0 (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq21094 eq810
    | (have j1 := eq21094 X0
       grind)
    | exact resolve eq810 eq21094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21094
  have eq21346 : ∀ X0 : G, (k X0 (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq21295 X0
       grind)
    | (have r₁ := eq21295 X0
       have r₂ := eq64
       grind)
    | exact resolve eq21295 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21295
  have eq21423 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X1 (M.op X1 (k (M.op (σ x) (σ y)) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21346 eq649
    | (have j1 := eq21346 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq649 eq21346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq21481 : ∀ X1 : G, (σ y) = (M.op X1 (M.op X1 (k (M.op (σ x) (σ y)) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X1
    first
    | exact superpose eq51 eq21423
    | exact resolve eq21423 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21423
  have eq21906 : ∀ X0 : G, (M.op X0 (k (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq21481 eq810
    | exact resolve eq810 eq21481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21949 : ∀ X0 : G, (M.op X0 (k (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq21906 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21906
  have eq36283 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq21949
    | (have j0 := eq21949 (σ x)
       grind)
    | exact resolve eq21949 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21949
  have eq36610 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq36283 eq21481
    | exact resolve eq21481 eq36283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21481 eq36283
  have eq36652 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq36610
  have eq36663 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (σ x) (σ y)) X1) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq36652 eq680
    | exact resolve eq680 eq36652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq36689 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq36652 eq658
    | exact resolve eq658 eq36652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq36652
  have eq36714 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq36689
    | (have j0 := eq36689 X0
       grind)
    | exact resolve eq36689 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36689
  have eq36728 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (σ x) (σ y)) X1) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq36663
    | (have j0 := eq36663 X0 X1
       grind)
    | exact resolve eq36663 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36663
  have eq37092 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq36714 eq810
    | exact resolve eq810 eq36714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq36714
  have eq37166 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq37092 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37092
  have eq37632 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (M.op (σ x) (σ y)) X0))) = X0 ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 X1 x
       have i₂ := eq36728 x X0
       grind)
    | exact superpose eq36728 eq659
    | exact resolve eq659 eq36728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq37679 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq901 x
       have i₂ := eq36728 x (M.op sF3 sF4)
       grind)
    | exact superpose eq36728 eq901
    | exact resolve eq901 eq36728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq36728
  have eq38029 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq37679
  have eq84282 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq37166 eq38029
    | exact resolve eq38029 eq37166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37166 eq38029
  have eq84364 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq84282
  have eq84442 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq84364 eq37632
    | exact resolve eq37632 eq84364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37632 eq84364
  have eq84522 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq84442
  have eq84865 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq84522 eq13869
    | exact resolve eq13869 eq84522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84522
  have eq84890 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq84865
  have eq84899 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq84890 eq1184
    | exact resolve eq1184 eq84890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq85340 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq84899 eq516
    | exact resolve eq516 eq84899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq84899
  have eq85628 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq51 eq85340
    | exact resolve eq85340 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85340
  have eq86490 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq85628 eq21346
    | (have j0 := eq21346 (σ y)
       grind)
    | exact resolve eq21346 eq85628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21346 eq85628
  have eq86554 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq86490
  have eq86560 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq86554
       have r₂ := eq64
       grind)
    | exact resolve eq86554 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86554
  have eq86562 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq86560
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq86560
    | exact resolve eq86560 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq86560
  have eq87862 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq86562 eq84890
    | exact resolve eq84890 eq86562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84890 eq86562
  have eq87936 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq87862
  have eq87959 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq87936
       have r₂ := eq64
       grind)
    | exact resolve eq87936 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq87936
  have eq87967 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq87959 eq57
    | exact resolve eq57 eq87959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87959
  have eq476437 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq5300
    | (have j0 := eq5300 (σ x) (σ y)
       grind)
    | exact resolve eq5300 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5300
  have eq476611 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq476437
       have r₂ := eq13869
       grind)
    | exact resolve eq476437 eq13869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13869 eq476437
  have eq476994 : (k x y) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq476611 eq57
    | exact resolve eq57 eq476611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq476611
  have eq477056 : (k x y) = (M.op x x) := by
    first
    | exact superpose eq71 eq476994
    | exact resolve eq476994 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476994
  have eq477068 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq477056
       have i₂ := eq87967
       grind)
    | exact superpose eq87967 eq477056
    | exact resolve eq477056 eq87967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87967
  have eq477187 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ (τ (M.op (σ x) (σ y)))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq479 x X0
       have i₂ := eq477068
       grind)
    | exact superpose eq477068 eq479
    | exact resolve eq479 eq477068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq477068
  have eq477865 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq477187 X0
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq477187
    | exact resolve eq477187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477187
  have eq477908 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq477865 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq477865
    | (have j0 := eq477865 X0
       grind)
    | exact resolve eq477865 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477865
  have eq477920 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq51 eq477908
    | exact resolve eq477908 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq477908
  have eq493191 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq124 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | (have j0 := eq124 x
       grind)
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq493325 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq20 eq493191
    | exact resolve eq493191 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493191
  have eq493375 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq493325
       have i₂ := eq477056
       grind)
    | exact superpose eq477056 eq493325
    | exact resolve eq493325 eq477056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477056 eq493325
  have eq493435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq493375 eq477920
    | exact resolve eq477920 eq493375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477920 eq493375
  have eq494201 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq493435
       have r₂ := eq27
       grind)
    | exact resolve eq493435 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493435
  have eq494806 : ∀ X0 : G, x = (M.op (τ (M.op X0 X0)) (M.op x (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1015 X0 x x
       have i₂ := eq494201
       grind)
    | exact superpose eq494201 eq1015
    | exact resolve eq1015 eq494201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq494201
  have eq494899 : (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1016 eq494806
    | exact resolve eq494806 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016 eq494806
  have eq495089 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq494899 eq29
    | exact resolve eq29 eq494899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq494899
  have eq495722 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq495089
    | exact resolve eq495089 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq495089
  have eq495723 : x = y := by grind
  clear eq495722
  have eq496003 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq495723
       grind)
    | exact superpose eq495723 eq18
    | exact resolve eq18 eq495723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq496004 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq495723
       grind)
    | exact superpose eq495723 eq24
    | exact resolve eq24 eq495723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq495723
  have eq496373 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq496004
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq496004
    | exact resolve eq496004 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq496004
  have eq496395 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq496373 eq26
    | exact resolve eq26 eq496373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq496373
  have eq498978 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq496395 eq71
    | exact resolve eq71 eq496395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq496395
  have eq499699 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq498978
       have i₂ := eq496003
       grind)
    | exact superpose eq496003 eq498978
    | exact resolve eq498978 eq496003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496003 eq498978
  have eq499940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq499699 eq15
    | exact resolve eq15 eq499699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499699
  have eq500020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq499940
    | exact resolve eq499940 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq499940
  have eq500111 : False := by grind
  exact eq500111

/-- `Equation1594`: `x = (y ◇ z) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_x_pyx_pyy_pyx_Equation1594 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1594 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1594.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X3 (M.op X2 X0)) (M.op (M.op X2 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X1)) X3 (M.op X2 X0)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq56
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq56
    | exact resolve eq56 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq59 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq125 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq125 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq125
    | (have j0 := eq125 (σ X0) (σ X1)
       grind)
    | exact resolve eq125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq125 X0 (τ X1)
       grind)
    | exact superpose eq125 eq18
    | (have j1 := eq125 X0 (τ X1)
       grind)
    | exact resolve eq18 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq125
  have eq273 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 (M.op (M.op X0 X1) X2) X0 x
       have i₂ := eq9 X2 x (M.op X0 X1)
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq297 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X2) X0) X1 X2
       have i₂ := eq273 X3 X2 X0
       grind)
    | exact superpose eq273 eq9
    | exact resolve eq9 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X2) X0)) = (M.op (M.op X3 X2) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X1 X2) X0)) X3 X2
       have i₂ := eq273 X1 X2 X0
       grind)
    | exact superpose eq273 eq9
    | exact resolve eq9 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) X2 (σ X0)
       have i₂ := eq126 X0 X1
       grind)
    | exact superpose eq126 eq9
    | (have j1 := eq126 X0 X1
       grind)
    | exact resolve eq9 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq553 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X0)) (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq539 X0 X1 X2
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq539
    | (have j0 := eq539 X0 X1 X2
       grind)
    | exact resolve eq539 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq771 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133
    | exact resolve eq133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq812 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq771 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq771
    | (have j0 := eq771 X0 X1
       grind)
    | exact resolve eq771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq1129 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X3 X0) (M.op X0 X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq300 (M.op X0 X1) X3 X0 x
       have i₂ := eq9 X1 x X0
       grind)
    | exact superpose eq9 eq300
    | exact resolve eq300 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1446 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1129 (σ X0) X1 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq1129
    | exact resolve eq1129 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1129 (τ X0) X1 (τ X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq1129
    | exact resolve eq1129 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1530 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1446 X0 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq1446
    | exact resolve eq1446 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1559 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1530 X0
       have i₂ := eq60 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq1530
    | exact resolve eq1530 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1690 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1452 X0 (τ X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq1452
    | exact resolve eq1452 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq1720 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1690 X0
       have i₂ := eq59 (M.op X0 X0)
       grind)
    | exact superpose eq59 eq1690
    | exact resolve eq1690 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1690
  have eq1743 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X1 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1559 X0
       have i₂ := eq297 (M.op X0 X0) X0 X0 X1
       grind)
    | (have i₁ := eq1559 X0
       have i₂ := eq297 (M.op X0 X0) X1 X0 X0
       grind)
    | exact superpose eq297 eq1559
    | exact resolve eq1559 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq1804 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1720 X0
       have i₂ := eq300 X0 X1 X0 X0
       grind)
    | exact superpose eq300 eq1720
    | exact resolve eq1720 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq1806 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X1 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1720 X0
       have i₂ := eq297 (M.op X0 X0) X0 X0 X1
       grind)
    | (have i₁ := eq1720 X0
       have i₂ := eq297 (M.op X0 X0) X1 X0 X0
       grind)
    | exact superpose eq297 eq1720
    | exact resolve eq1720 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq1720
  have eq2248 : ∀ X0 X1 : G, (M.op X0 (τ (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1804 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1804
    | exact resolve eq1804 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804
  have eq2411 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1806 (σ X0) X1
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq1806
    | exact resolve eq1806 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1806
  have eq2456 : ∀ X0 X1 : G, (M.op X0 (τ (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2411 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2411
    | exact resolve eq2411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq3628 : ∀ X1 X2 : G, (M.op X1 (τ (σ X2))) = X1 ∨ (σ (k X1 X2)) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq2456 X1 x
       have i₂ := eq553 X1 X2 x
       grind)
    | exact superpose eq553 eq2456
    | (have j1 := eq553 X1 X2 X2
       grind)
    | exact resolve eq2456 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq2456
  have eq3702 : ∀ X1 X2 : G, (σ (k X1 X2)) = (M.op (σ X2) (σ X1)) ∨ (M.op X1 X2) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq3628 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq3628
    | (have j0 := eq3628 X1 X2
       grind)
    | exact resolve eq3628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3628
  have eq7159 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3702 y x
       grind)
    | exact superpose eq3702 eq16
    | (have j1 := eq3702 y x
       grind)
    | exact resolve eq16 eq3702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3702
  have eq7215 : y = (M.op y x) := by
    first
    | (have j1 := eq812 x y
       grind)
    | (have r₁ := eq7159
       have r₂ := eq812 x y
       grind)
    | exact resolve eq7159 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq7159
  have eq7220 : ∀ X0 : G, (M.op y (M.op x (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq7215
       grind)
    | exact superpose eq7215 eq9
    | exact resolve eq9 eq7215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7221 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq7215
       grind)
    | exact superpose eq7215 eq9
    | exact resolve eq9 eq7215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7232 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq273 y x X0
       have i₂ := eq7215
       grind)
    | exact superpose eq7215 eq273
    | exact resolve eq273 eq7215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq7320 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1743 y x
       have i₂ := eq7221 x
       grind)
    | exact superpose eq7221 eq1743
    | exact resolve eq1743 eq7221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743 eq7221
  have eq7567 : x = (M.op x (τ (M.op (σ x) (M.op (σ y) (σ x))))) := by
    first
    | (have i₁ := eq2248 x (σ y)
       have i₂ := eq7320
       grind)
    | exact superpose eq7320 eq2248
    | exact resolve eq2248 eq7320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248
  have eq7613 : x = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7567
       have i₂ := eq7320
       grind)
    | exact superpose eq7320 eq7567
    | exact resolve eq7567 eq7320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7320 eq7567
  have eq7625 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq7232 x
       have i₂ := eq7215
       grind)
    | exact superpose eq7215 eq7232
    | exact resolve eq7232 eq7215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7215 eq7232
  have eq7673 : (M.op x y) = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq7220 (M.op x y)
       have i₂ := eq7625
       grind)
    | exact superpose eq7625 eq7220
    | exact resolve eq7220 eq7625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7625
  have eq8913 : (M.op y (M.op x x)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7220 (τ (M.op (σ x) (σ y)))
       have i₂ := eq7613
       grind)
    | exact superpose eq7613 eq7220
    | exact resolve eq7220 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7220 eq7613
  have eq8960 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq8913
       have i₂ := eq7673
       grind)
    | exact superpose eq7673 eq8913
    | exact resolve eq8913 eq7673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7673 eq8913
  have eq9094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq8960
       grind)
    | exact superpose eq8960 eq11
    | exact resolve eq11 eq8960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8960
  have eq9121 : False := by grind
  exact eq9121

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq56 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq79
    | exact resolve eq79 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq81
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81
    | exact resolve eq81 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq89 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq59 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq59 X1 X3 x
       have i₂ := eq59 X1 X0 x
       grind)
    | (have i₁ := eq59 X0 X1 X0
       have i₂ := eq59 X0 X0 x
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 x X2
       have i₂ := eq59 X0 x X1
       grind)
    | (have i₁ := eq59 X2 X2 X2
       have i₂ := eq59 X2 X1 X2
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq56 eq59
    | exact resolve eq59 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq59 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq59 X0 X0 X2
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq933 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq373 sF0
       have i₂ := eq371 sF0 x x
       grind)
    | (have i₁ := eq373 sF0
       have i₂ := eq371 sF0 x x
       grind)
    | exact superpose eq371 eq373
    | exact resolve eq373 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq955 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq374 sF4
       have i₂ := eq371 sF4 x sF2
       grind)
    | (have i₁ := eq374 sF4
       have i₂ := eq371 sF4 sF2 x
       grind)
    | exact superpose eq371 eq374
    | exact resolve eq374 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq374
  have eq1052 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq358 X3 X1 x
       have i₂ := eq358 X0 X1 x
       grind)
    | (have i₁ := eq358 X0 X1 X3
       have i₂ := eq358 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq358 eq358
    | exact resolve eq358 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1063 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq358 X0 (M.op X1 X1) X3
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq358 X0 (M.op X1 X1) X3
       have i₂ := eq358 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq358 eq358
    | exact resolve eq358 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1096 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X1)
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq56 (M.op X1 X1)
       have i₂ := eq358 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq358 eq56
    | exact resolve eq56 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1097 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X1 X1)
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq57 (M.op X1 X1)
       have i₂ := eq358 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq358 eq57
    | exact resolve eq57 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1104 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op X1 X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (M.op X1 X1)
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq215 (M.op X1 X1)
       have i₂ := eq358 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq358 eq215
    | exact resolve eq215 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1105 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op (M.op X3 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq370 (M.op X1 X1) X2 X3
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq370 (M.op X1 X1) X1 X3
       have i₂ := eq358 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq358 eq370
    | exact resolve eq370 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1107 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X1 X1)) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq378 (M.op X1 X1) X3 X2
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq378 (M.op X1 X1) X1 X2
       have i₂ := eq358 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq358 eq378
    | exact resolve eq378 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq378
  have eq1146 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1063 X0 X1 x X3
       have i₂ := eq58 X0 x X1
       grind)
    | exact superpose eq58 eq1063
    | exact resolve eq1063 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq1063
  have eq1163 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) = (M.op (M.op X1 X1) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq933 eq59
    | exact resolve eq59 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq1167 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1163 x x
       have i₂ := eq14 sF0 x x
       grind)
    | exact superpose eq14 eq1163
    | exact resolve eq1163 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1239 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) = (M.op (M.op X1 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq955 eq59
    | exact resolve eq59 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq955
  have eq1243 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1239 x x
       have i₂ := eq14 sF4 x x
       grind)
    | exact superpose eq14 eq1239
    | exact resolve eq1239 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1459 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1167 (M.op X1 X1)
       have i₂ := eq1052 sF0 X1 x
       grind)
    | (have i₁ := eq1167 (M.op X1 X1)
       have i₂ := eq1052 X0 X1 sF0
       grind)
    | exact superpose eq1052 eq1167
    | exact resolve eq1167 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1462 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 X1)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1243 (M.op X1 X1)
       have i₂ := eq1052 sF4 X1 x
       grind)
    | (have i₁ := eq1243 (M.op X1 X1)
       have i₂ := eq1052 X0 X1 sF4
       grind)
    | exact superpose eq1052 eq1243
    | exact resolve eq1243 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq13460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq13461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13460
    | exact resolve eq13460 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13460
  have eq13472 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq13461
       have r₂ := eq27
       grind)
    | exact resolve eq13461 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13461
  have eq13474 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13472
    | exact resolve eq13472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13472
  have eq13590 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13474 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13474
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13474
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13474
       grind)
    | exact resolve eq13 eq13474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13474
  have eq13601 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq13590
  have eq13610 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13601 eq55
    | exact resolve eq55 eq13601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq13601
  have eq13637 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq13610
    | exact resolve eq13610 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13610
  have eq13640 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq13637
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13637
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq13637
       have r₂ := eq13 x y
       grind)
    | exact resolve eq13637 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13637
  have eq13766 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq802 x y
       have i₂ := eq13640
       grind)
    | exact superpose eq13640 eq802
    | (have j0 := eq802 x y
       grind)
    | exact resolve eq802 eq13640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13768 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq13640
       grind)
    | exact superpose eq13640 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq13640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13640
  have eq13769 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13768
  have eq13771 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13766
  have eq13774 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13769
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13769
    | exact resolve eq13769 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13769
  have eq13775 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13774
  have eq13777 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13771
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13771
    | exact resolve eq13771 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13771
  have eq13791 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13777
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13777
    | exact resolve eq13777 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13777
  have eq13796 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13791
    | exact resolve eq13791 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13791
  have eq13797 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13796
  have eq13802 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13797
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13797
    | exact resolve eq13797 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13797
  have eq13808 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13802
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13802
    | exact resolve eq13802 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13802
  have eq13815 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq13775
       grind)
    | exact superpose eq13775 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13775
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13775
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13775
       grind)
    | exact resolve eq12 eq13775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13775
  have eq13828 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13815
  have eq13829 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13828
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13828
    | exact resolve eq13828 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13828
  have eq13830 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13829
  have eq13831 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13830
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13830
    | exact resolve eq13830 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13830
  have eq13984 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13808 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13808
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13808
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13808
       grind)
    | exact resolve eq12 eq13808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13808
  have eq13997 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13984
  have eq13998 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13997
    | exact resolve eq13997 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13997
  have eq13999 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13998
  have eq14000 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13999
    | exact resolve eq13999 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13999
  have eq14002 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq89
       have i₂ := eq13831
       grind)
    | exact superpose eq13831 eq89
    | exact resolve eq89 eq13831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13831
  have eq14026 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14002
    | exact resolve eq14002 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14002
  have eq14241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14026 eq14000
    | exact resolve eq14000 eq14026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14000 eq14026
  have eq14248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14241
  have eq14250 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14248
       have r₂ := eq27
       grind)
    | exact resolve eq14248 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14248
  have eq14262 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14250 eq51
    | (have r₁ := eq51
       have r₂ := eq14250
       grind)
    | exact resolve eq51 eq14250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq14272 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (M.op X1 X1)) (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq14250 eq1462
    | exact resolve eq1462 eq14250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14274 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq14262
  have eq14275 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1104 eq14272
    | exact resolve eq14272 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq14272
  have eq14398 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14274 eq99
    | exact resolve eq99 eq14274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq14274
  have eq14429 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq14398
    | exact resolve eq14398 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14398
  have eq14433 : y = (k y x) := by
    first
    | (have r₁ := eq14429
       have r₂ := eq50
       grind)
    | exact resolve eq14429 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq14429
  have eq14550 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq89
       have i₂ := eq14433
       grind)
    | exact superpose eq14433 eq89
    | exact resolve eq89 eq14433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14561 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq802 y x
       have i₂ := eq14433
       grind)
    | exact superpose eq14433 eq802
    | (have j0 := eq802 y x
       grind)
    | exact resolve eq802 eq14433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq14563 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq14433
       grind)
    | exact superpose eq14433 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq14433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14564 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq14563
  have eq14566 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14561
  have eq14569 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14564
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14564
    | exact resolve eq14564 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14564
  have eq14571 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14566
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14566
    | exact resolve eq14566 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14566
  have eq14581 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq14550
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14550
    | exact resolve eq14550 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14550
  have eq14584 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14571
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14571
    | exact resolve eq14571 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14571
  have eq14589 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq14584
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14584
    | exact resolve eq14584 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14584
  have eq14594 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq14589
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14589
    | exact resolve eq14589 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14589
  have eq14599 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14594
    | exact resolve eq14594 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14594
  have eq14786 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14569
       grind)
    | exact superpose eq14569 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14569
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14569
       grind)
    | exact resolve eq12 eq14569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14799 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq14786
  have eq14800 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14799
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14799
    | exact resolve eq14799 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14799
  have eq14801 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq14800
  have eq14802 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14801
       have i₂ := eq14433
       grind)
    | exact superpose eq14433 eq14801
    | exact resolve eq14801 eq14433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14433 eq14801
  have eq14803 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14802
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14802
    | exact resolve eq14802 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14802
  have eq14996 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq16259 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14250 eq14275
    | exact resolve eq14275 eq14250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14250 eq14275
  have eq16276 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq16259
  have eq16314 : x = (M.op (σ x) (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16276 eq1096
    | exact resolve eq1096 eq16276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq16319 : (M.op x y) = (M.op x (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16276 eq1459
    | exact resolve eq1459 eq16276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459 eq16276
  have eq16484 : x = (M.op (σ x) (M.op y x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14803 eq16314
    | exact resolve eq16314 eq14803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16314
  have eq16504 : x = (M.op (σ x) (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16484
       have r₂ := eq14996
       grind)
    | exact resolve eq16484 eq14996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16484
  have eq16666 : y = (M.op x (M.op (σ x) y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14803 eq16319
    | exact resolve eq16319 eq14803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14803 eq16319
  have eq16682 : y = (M.op x (M.op (σ x) y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16666
       have r₂ := eq14996
       grind)
    | exact resolve eq16666 eq14996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14996 eq16666
  have eq18075 : x = (M.op (σ x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16504
       have i₂ := eq14569
       grind)
    | exact superpose eq14569 eq16504
    | exact resolve eq16504 eq14569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14569 eq16504
  have eq18092 : x = (M.op (σ x) y) ∨ x = (M.op x y) := by grind
  clear eq18075
  have eq18255 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18092 eq16682
    | exact resolve eq16682 eq18092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16682
  have eq18270 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq18255
  have eq18312 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1052 X0 x x
       have i₂ := eq18270
       grind)
    | exact superpose eq18270 eq1052
    | exact resolve eq1052 eq18270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq18270
  have eq21333 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18312 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18312
    | (have j0 := eq18312 x X0
       grind)
    | exact resolve eq18312 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18312
  have eq21635 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18092
       have i₂ := eq21333 sF2
       grind)
    | exact superpose eq21333 eq18092
    | exact resolve eq18092 eq21333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18092 eq21333
  have eq21639 : x = (M.op x y) := by grind
  clear eq21635
  have eq21649 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21639 eq20
    | exact resolve eq20 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq21655 : (σ (k y x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21639 eq91
    | exact resolve eq91 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq21639
  have eq21785 : (k (σ y) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq21655
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq21655
    | exact resolve eq21655 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq21655
  have eq21789 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21649
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21649
    | exact resolve eq21649 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21649
  have eq21805 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq14581 eq21785
    | exact resolve eq21785 eq14581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14581 eq21785
  have eq21811 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21789 eq26
    | exact resolve eq26 eq21789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq21896 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21789 eq14599
    | exact resolve eq14599 eq21789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14599
  have eq21928 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq21896
       have r₂ := eq27
       grind)
    | exact resolve eq21896 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21896
  have eq22374 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21928 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq21928
       grind)
    | exact resolve eq12 eq21928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22388 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq22374
  have eq22389 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21811 eq22388
    | exact resolve eq22388 eq21811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22388
  have eq22390 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq22389
       have r₂ := eq27
       grind)
    | exact resolve eq22389 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22389
  have eq22391 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21811 eq22390
    | exact resolve eq22390 eq21811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22390
  have eq22392 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21805 eq22391
    | exact resolve eq22391 eq21805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21805 eq22391
  have eq23454 : ∀ X0 X1 X2 X3 : G, (σ x) = (M.op (M.op X3 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1097 X3 (M.op X2 X2)
       have i₂ := eq1105 X0 X1 (M.op X2 X2) X2
       grind)
    | (have i₁ := eq1097 X0 (M.op X0 (M.op X1 X1))
       have i₂ := eq1105 X0 X1 (M.op X0 (M.op X1 X1)) X3
       grind)
    | exact superpose eq1105 eq1097
    | exact resolve eq1097 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq1105
  have eq23514 : ∀ X0 X1 X2 X3 : G, (σ (M.op x y)) = (M.op (M.op X3 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2))) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq21789 eq23454
    | exact resolve eq23454 eq21789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23454
  have eq23615 : ∀ X0 X1 X2 X3 : G, (σ (M.op x y)) = (M.op (M.op X3 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2))) (M.op (σ y) (σ (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq22392 eq23514
    | exact resolve eq23514 eq22392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23514
  have eq23657 : ∀ X0 X1 X2 X3 : G, (σ (M.op x y)) = (M.op (M.op X3 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2))) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq21928 eq23615
    | exact resolve eq23615 eq21928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21928 eq23615
  have eq23684 : ∀ X2 : G, (σ (M.op x y)) = (M.op (M.op X2 X2) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq23657 x x X2 x
       have i₂ := eq1146 (M.op x (M.op x x)) X2 x
       grind)
    | exact superpose eq1146 eq23657
    | exact resolve eq23657 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23657
  have eq24166 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1462 X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))
       have i₂ := eq1107 X0 X1 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq1107 eq1462
    | exact resolve eq1462 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq1462
  have eq24188 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ x) (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq22392 eq24166
    | exact resolve eq24166 eq22392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22392 eq24166
  have eq24236 : ∀ X1 : G, (σ y) = (M.op (σ x) (M.op (M.op X1 X1) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq24188 x X1 x
       have i₂ := eq1146 x X1 x
       grind)
    | exact superpose eq1146 eq24188
    | exact resolve eq24188 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146 eq24188
  have eq24250 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23684 eq24236
    | exact resolve eq24236 eq23684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24236
  have eq24259 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21789 eq24250
    | exact resolve eq24250 eq21789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21789 eq24250
  have eq24322 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq24259 eq23684
    | exact resolve eq23684 eq24259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24259
  have eq24431 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24322 eq23684
    | exact resolve eq23684 eq24322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23684 eq24322
  have eq24456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21811 eq24431
    | exact resolve eq24431 eq21811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21811 eq24431
  have eq24488 : False := by grind
  exact eq24488
