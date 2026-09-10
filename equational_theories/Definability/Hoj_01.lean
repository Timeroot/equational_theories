import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation2291 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq15
    | exact resolve eq15 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq74
    | exact resolve eq74 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq74
  have eq99 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq101 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq99
    | exact resolve eq99 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq104 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq101
  have eq184 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq186 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq189 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 X1
       have i₂ := eq81 X1
       grind)
    | exact superpose eq81 eq184
    | (have j0 := eq184 X0 X1
       grind)
    | exact resolve eq184 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq628 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq189 x y
       grind)
    | exact superpose eq189 eq16
    | (have j1 := eq189 x y
       grind)
    | exact resolve eq16 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1050 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq186 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq186
    | exact resolve eq186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1050 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1050
    | (have j0 := eq1050 X0 X1
       grind)
    | exact resolve eq1050 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq5177 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq628
       have i₂ := eq1105 x y
       grind)
    | exact superpose eq1105 eq628
    | (have j1 := eq1105 x y
       grind)
    | (have r₁ := eq628
       have r₂ := eq1105 x y
       grind)
    | (have r₁ := eq628
       have r₂ := eq1105 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq628
       have r₂ := eq1105 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq628 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq1105
  have eq5178 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq5177
  have eq5180 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5178
       grind)
    | exact superpose eq5178 eq16
    | exact resolve eq16 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178
  have eq5181 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5180
       have r₂ := eq81 x
       grind)
    | exact resolve eq5180 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5180
  have eq5191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq104 y
       have i₂ := eq5181
       grind)
    | exact superpose eq5181 eq104
    | exact resolve eq104 eq5181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5181
  have eq5211 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq5191
       have r₂ := eq16
       grind)
    | exact resolve eq5191 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5191
  have eq5215 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5211
       grind)
    | exact superpose eq5211 eq10
    | exact resolve eq10 eq5211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5211
  have eq5269 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5215
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5215
    | exact resolve eq5215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5215
  have eq5272 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5269
       grind)
    | exact superpose eq5269 eq16
    | exact resolve eq16 eq5269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5269
  have eq5273 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq5272
       have r₂ := eq81 x
       grind)
    | exact resolve eq5272 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq5272
  have eq5285 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5273
       grind)
    | exact superpose eq5273 eq10
    | exact resolve eq10 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273
  have eq5339 : x = (M.op y y) := by
    first
    | (have i₁ := eq5285
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5285
    | exact resolve eq5285 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5285
  have eq5355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104 y
       have i₂ := eq5339
       grind)
    | exact superpose eq5339 eq104
    | exact resolve eq104 eq5339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq5339
  have eq5374 : False := by grind
  exact eq5374

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  clear eq43
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
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
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
  have eq150 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ y)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq386 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq14
    | exact resolve eq14 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq652 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq94 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq654 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq652 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq912 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59 eq386
    | exact resolve eq386 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq386
    | exact resolve eq386 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq931 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq912 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3837 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq654 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq654
    | (have j0 := eq654 (τ X0)
       grind)
    | exact resolve eq654 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq654
  have eq3845 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
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
  have eq3851 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3845 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3845
    | (have j0 := eq3845 X0
       grind)
    | exact resolve eq3845 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845
  have eq10657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10657
    | exact resolve eq10657 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10657
  have eq10669 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10658
       have r₂ := eq27
       grind)
    | exact resolve eq10658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10658
  have eq10671 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10669
    | exact resolve eq10669 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10669
  have eq10695 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10671 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq10671
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10671
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10671
       grind)
    | exact resolve eq13 eq10671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10671
  have eq10730 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq10695
  have eq10763 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10730 eq49
    | exact resolve eq49 eq10730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq10730
  have eq10797 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq10763
    | exact resolve eq10763 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10763
  have eq10801 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3851 x
       grind)
    | (have r₁ := eq10797
       have r₂ := eq3851 x
       grind)
    | exact resolve eq10797 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851 eq10797
  have eq10802 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq10801
       grind)
    | exact superpose eq10801 eq56
    | exact resolve eq56 eq10801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10803 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq10801
       grind)
    | exact superpose eq10801 eq59
    | exact resolve eq59 eq10801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10823 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq69 X0 x
       have i₂ := eq10801
       grind)
    | exact superpose eq10801 eq69
    | (have j0 := eq69 X0 x
       grind)
    | (have r₁ := eq69 X0 x
       have r₂ := eq10801
       grind)
    | exact resolve eq69 eq10801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq10824 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq10801
       grind)
    | exact superpose eq10801 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq10801
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10801
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10801
       grind)
    | exact resolve eq13 eq10801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10801
  have eq10859 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10824
  have eq10860 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10823 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10823
  have eq10886 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq912 eq10803
    | exact resolve eq10803 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10803
  have eq10902 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq653 x x
       have i₂ := eq10859
       grind)
    | exact superpose eq10859 eq653
    | (have j0 := eq653 x x
       grind)
    | exact resolve eq653 eq10859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10859
  have eq10905 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10902
  have eq10906 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10905
  have eq10914 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10906
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10906
    | exact resolve eq10906 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10906
  have eq10947 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq10860 y
       grind)
    | exact superpose eq10860 eq75
    | exact resolve eq75 eq10860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10860
  have eq11009 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10947
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10947
    | exact resolve eq10947 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10947
  have eq11036 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11009
       have r₂ := eq51
       grind)
    | exact resolve eq11009 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq11009
  have eq11193 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11036 eq82
    | exact resolve eq82 eq11036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq11194 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11036 eq117
    | exact resolve eq117 eq11036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq11036
  have eq11203 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11194
  have eq11212 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq11193
    | exact resolve eq11193 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11193
  have eq11217 : y = (k y x) := by
    first
    | (have r₁ := eq11212
       have r₂ := eq50
       grind)
    | exact resolve eq11212 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq11212
  have eq11220 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11217
       grind)
    | exact superpose eq11217 eq75
    | exact resolve eq75 eq11217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq11228 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq11217
       grind)
    | exact superpose eq11217 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq11217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11217
  have eq11229 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11228
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11228
    | exact resolve eq11228 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11228
  have eq11237 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11220
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11220
    | exact resolve eq11220 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11220
  have eq11239 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11229
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11229
    | exact resolve eq11229 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11229
  have eq11334 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10914 eq57
    | exact resolve eq57 eq10914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq11335 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10914 eq60
    | exact resolve eq60 eq10914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq10914
  have eq11419 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq915 eq11335
    | exact resolve eq11335 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11335
  have eq11609 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq11203
       grind)
    | exact superpose eq11203 eq56
    | exact resolve eq56 eq11203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11610 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq11203
       grind)
    | exact superpose eq11203 eq59
    | exact resolve eq59 eq11203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq11203
  have eq11697 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq912 eq11610
    | exact resolve eq11610 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11610
  have eq11788 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq11239
       grind)
    | exact superpose eq11239 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq11239
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq11239
       grind)
    | exact resolve eq13 eq11239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11239
  have eq11823 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq11788
  have eq12324 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq653 x x
       have i₂ := eq11823
       grind)
    | exact superpose eq11823 eq653
    | (have j0 := eq653 x x
       grind)
    | exact resolve eq653 eq11823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11823
  have eq12327 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12324
  have eq12328 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12327
  have eq12336 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12328
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12328
    | exact resolve eq12328 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12328
  have eq31370 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10886 eq10802
    | exact resolve eq10802 eq10886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10802 eq10886
  have eq31418 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31370
  have eq31422 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31418
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31418
    | exact resolve eq31418 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31418
  have eq31432 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31422 eq216
    | exact resolve eq216 eq31422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31422
  have eq32104 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11419 eq11334
    | exact resolve eq11334 eq11419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11334 eq11419
  have eq32153 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32104
  have eq32157 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq32153
    | exact resolve eq32153 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32153
  have eq32368 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32157 eq27
    | exact resolve eq27 eq32157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32157
  have eq33695 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12336 eq31432
    | exact resolve eq31432 eq12336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12336 eq31432
  have eq33757 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq33695
  have eq33760 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq33757
    | exact resolve eq33757 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33757
  have eq33953 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33760 eq27
    | exact resolve eq27 eq33760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33760
  have eq46260 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11697 eq11609
    | exact resolve eq11609 eq11697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11609 eq11697
  have eq46313 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq46260
  have eq46318 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq46313
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq46313
    | exact resolve eq46313 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46313
  have eq46321 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq46318
       have r₂ := eq33953
       grind)
    | exact resolve eq46318 eq33953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33953 eq46318
  have eq46324 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46321 eq20
    | exact resolve eq20 eq46321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46321
  have eq46522 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46324
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46324
    | exact resolve eq46324 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46324
  have eq46946 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46522 eq11237
    | exact resolve eq11237 eq46522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11237
  have eq46978 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46522 eq32368
    | (have r₁ := eq32368
       have r₂ := eq46522
       grind)
    | exact resolve eq32368 eq46522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32368
  have eq47018 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46978
  have eq47019 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq47018
  have eq47431 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47019 eq216
    | exact resolve eq216 eq47019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq47461 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47019 eq915
    | exact resolve eq915 eq47019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq47019
  have eq48002 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46946 eq150
    | exact resolve eq150 eq46946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq46946
  have eq48035 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq48002
    | exact resolve eq48002 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq48002
  have eq48038 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have r₁ := eq48035
       have r₂ := eq931
       grind)
    | exact resolve eq48035 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq48035
  have eq56865 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47461 eq47431
    | exact resolve eq47431 eq47461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47431 eq47461
  have eq56933 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq56865
  have eq56944 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq56933
    | exact resolve eq56933 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56933
  have eq56950 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56944 eq27
    | exact resolve eq27 eq56944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56944
  have eq57040 : x = (M.op x y) := by
    first
    | (have r₁ := eq56950
       have r₂ := eq46522
       grind)
    | exact resolve eq56950 eq46522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46522 eq56950
  have eq57044 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq57040 eq20
    | exact resolve eq20 eq57040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq57143 : x = (M.op x x) := by
    first
    | exact superpose eq57040 eq912
    | exact resolve eq912 eq57040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq57180 : x = (k x x) := by
    first
    | exact superpose eq57040 eq48038
    | exact resolve eq48038 eq57040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48038
  have eq57263 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq57044
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq57044
    | exact resolve eq57044 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57044
  have eq57300 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq57263 eq26
    | exact resolve eq26 eq57263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq57622 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq57143
       grind)
    | exact superpose eq57143 eq56
    | exact resolve eq56 eq57143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq57753 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq57040 eq57622
    | exact resolve eq57622 eq57040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57622
  have eq57780 : y = (M.op x y) := by
    first
    | (have i₁ := eq57753
       have i₂ := eq57143
       grind)
    | exact superpose eq57143 eq57753
    | exact resolve eq57753 eq57143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57143 eq57753
  have eq57790 : y = (M.op x y) := by
    first
    | (have i₁ := eq57780
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57780
    | exact resolve eq57780 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq57780
  have eq57797 : x = y := by
    first
    | exact superpose eq57040 eq57790
    | exact resolve eq57790 eq57040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57040 eq57790
  have eq57801 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq57797
       grind)
    | exact superpose eq57797 eq24
    | exact resolve eq24 eq57797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq57797
  have eq58033 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq57801
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq57801
    | exact resolve eq57801 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57801
  have eq58108 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq57263 eq58033
    | exact resolve eq58033 eq57263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58033
  have eq58571 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq653 x x
       have i₂ := eq57180
       grind)
    | exact superpose eq57180 eq653
    | (have j0 := eq653 x x
       grind)
    | exact resolve eq653 eq57180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq57180
  have eq58572 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq58571
  have eq58573 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq58572
  have eq58591 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq58573
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq58573
    | exact resolve eq58573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq58573
  have eq58611 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq57263 eq58591
    | exact resolve eq58591 eq57263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57263 eq58591
  have eq59206 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq58108 eq57300
    | exact resolve eq57300 eq58108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57300 eq58108
  have eq60856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58611 eq59206
    | exact resolve eq59206 eq58611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58611 eq59206
  have eq60857 : False := by grind
  exact eq60857

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq381 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq389 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq14
    | exact resolve eq14 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq700 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq711 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq700 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq714 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq711 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq711 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq711 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq711 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq724 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq714 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq714
    | (have j0 := eq714 X0 X1
       grind)
    | exact resolve eq714 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq1007 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq389
    | exact resolve eq389 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq389
    | exact resolve eq389 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1012 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq389
    | exact resolve eq389 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq389
  have eq10132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10132
    | exact resolve eq10132 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10132
  have eq10144 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10133
       have r₂ := eq28
       grind)
    | exact resolve eq10133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10133
  have eq10146 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10144
    | exact resolve eq10144 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10144
  have eq10166 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq10201 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10146 eq1007
    | exact resolve eq1007 eq10146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10146
  have eq10202 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10201
    | exact resolve eq10201 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10201
  have eq10223 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10202
  have eq10447 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq708 x y
       have i₂ := eq10223
       grind)
    | exact superpose eq10223 eq708
    | (have j0 := eq708 x y
       grind)
    | exact resolve eq708 eq10223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq10223
  have eq10546 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10447
  have eq10639 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10546
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10546
    | exact resolve eq10546 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10546
  have eq10731 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10639
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10639
    | exact resolve eq10639 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10639
  have eq10819 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10731
    | exact resolve eq10731 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10731
  have eq10820 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10819
  have eq10906 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10820
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10820
    | exact resolve eq10820 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10820
  have eq10992 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10906
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10906
    | exact resolve eq10906 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10906
  have eq11060 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10992 eq1007
    | exact resolve eq1007 eq10992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10992
  have eq11061 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11060
    | exact resolve eq11060 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11060
  have eq11062 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11061
  have eq11064 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11062 eq28
    | exact resolve eq28 eq11062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11062
  have eq13611 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10166 eq97
    | exact resolve eq97 eq10166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq10166
  have eq13637 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq13611
    | exact resolve eq13611 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13611
  have eq17479 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq13637
  have eq17515 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17479
  have eq17529 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq17515
       grind)
    | exact superpose eq17515 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17515
  have eq17539 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17529
  have eq17548 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17539
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17539
    | exact resolve eq17539 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17539
  have eq17549 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17548
  have eq17659 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1007 x x
       have i₂ := eq17549
       grind)
    | exact superpose eq17549 eq1007
    | exact resolve eq1007 eq17549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17549
  have eq17662 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17659
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17659
    | exact resolve eq17659 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17659
  have eq17667 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17662 eq28
    | exact resolve eq28 eq17662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17671 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17662 eq216
    | exact resolve eq216 eq17662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17694 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17662 eq1012
    | exact resolve eq1012 eq17662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20024 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17694 eq17671
    | exact resolve eq17671 eq17694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17671 eq17694
  have eq20074 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20024
  have eq20079 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq20074
    | exact resolve eq20074 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20074
  have eq20117 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20079 eq17662
    | exact resolve eq17662 eq20079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17662
  have eq20124 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20117
  have eq20165 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20124 eq27
    | exact resolve eq27 eq20124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20124
  have eq20798 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20165
  have eq20878 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20079 eq20798
    | exact resolve eq20798 eq20079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20079 eq20798
  have eq20901 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20878
  have eq21052 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20901 eq100
    | exact resolve eq100 eq20901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq20901
  have eq21071 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq21052
  have eq21086 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21071
       have r₂ := eq17667
       grind)
    | exact resolve eq21071 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17667 eq21071
  have eq21484 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1007 x x
       have i₂ := eq21086
       grind)
    | exact superpose eq21086 eq1007
    | exact resolve eq1007 eq21086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq21086
  have eq21489 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21484
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21484
    | exact resolve eq21484 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21484
  have eq21490 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21489
  have eq21520 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21490 eq21
    | exact resolve eq21 eq21490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21490
  have eq21663 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21520
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21520
    | exact resolve eq21520 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21520
  have eq21744 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21663 eq11064
    | (have r₁ := eq11064
       have r₂ := eq21663
       grind)
    | exact resolve eq11064 eq21663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11064
  have eq21781 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21744
  have eq21782 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21781
  have eq21880 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21782 eq216
    | exact resolve eq216 eq21782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq21905 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21782 eq1012
    | exact resolve eq1012 eq21782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq21782
  have eq28345 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21905 eq21880
    | exact resolve eq21880 eq21905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21880 eq21905
  have eq28403 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq28345
  have eq28415 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq28403
    | exact resolve eq28403 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28403
  have eq28423 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28415 eq28
    | exact resolve eq28 eq28415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28415
  have eq28503 : x = (M.op x y) := by
    first
    | (have r₁ := eq28423
       have r₂ := eq21663
       grind)
    | exact resolve eq28423 eq21663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21663 eq28423
  have eq28507 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28503 eq21
    | exact resolve eq21 eq28503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28586 : x = (M.op x x) := by
    first
    | exact superpose eq28503 eq1010
    | exact resolve eq1010 eq28503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq28657 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28507
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28507
    | exact resolve eq28507 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28507
  have eq28669 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq28657 eq27
    | exact resolve eq27 eq28657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq28847 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq28586
       grind)
    | exact superpose eq28586 eq47
    | exact resolve eq47 eq28586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq28871 : x = (k x x) := by grind
  have eq28961 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq28503 eq28847
    | exact resolve eq28847 eq28503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28847
  have eq28990 : y = (M.op x y) := by
    first
    | (have i₁ := eq28961
       have i₂ := eq28586
       grind)
    | exact superpose eq28586 eq28961
    | exact resolve eq28961 eq28586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28586 eq28961
  have eq29007 : y = (M.op x y) := by
    first
    | (have i₁ := eq28990
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28990
    | exact resolve eq28990 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28990
  have eq29015 : x = y := by
    first
    | exact superpose eq28503 eq29007
    | exact resolve eq29007 eq28503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28503 eq29007
  have eq29029 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq29015
       grind)
    | exact superpose eq29015 eq25
    | exact resolve eq25 eq29015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29015
  have eq29181 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29029
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29029
    | exact resolve eq29029 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29029
  have eq29245 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28657 eq29181
    | exact resolve eq29181 eq28657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29181
  have eq29505 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq29245 eq28669
    | exact resolve eq28669 eq29245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28669 eq29245
  have eq29587 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq724 x x
       have i₂ := eq28871
       grind)
    | exact superpose eq28871 eq724
    | (have j0 := eq724 x x
       grind)
    | exact resolve eq724 eq28871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq28871
  have eq29592 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29587
  have eq29593 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29592
  have eq29610 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq29593
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29593
    | exact resolve eq29593 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29593
  have eq29629 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28657 eq29610
    | exact resolve eq29610 eq28657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28657 eq29610
  have eq29739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29505 eq29629
    | exact resolve eq29629 eq29505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29505 eq29629
  have eq29740 : False := by grind
  exact eq29740

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 y
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq184 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq189 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq186 eq16
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq181 eq184
    | exact resolve eq184 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq551 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq548
       grind)
    | exact superpose eq548 eq16
    | exact resolve eq16 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq556 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq186 eq189
    | exact resolve eq189 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq189
  have eq559 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq556 eq16
    | exact resolve eq16 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq565 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq551 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq551
    | exact resolve eq551 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq575 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq559 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq559
    | exact resolve eq559 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq634 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
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
  have eq648 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq713 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq634
       grind)
    | exact superpose eq634 eq40
    | exact resolve eq40 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq634
  have eq714 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq713
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq713
    | exact resolve eq713 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq716 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq714
    | exact resolve eq714 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq716 eq648
    | exact resolve eq648 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq733 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq726
       have r₂ := eq27
       grind)
    | exact resolve eq726 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq738 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq733 eq575
    | exact resolve eq575 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq733 eq16
    | exact resolve eq16 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq575 eq742
    | exact resolve eq742 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq742
  have eq761 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq738 eq744
    | exact resolve eq744 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq769 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq761
  have eq791 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq769 eq733
    | exact resolve eq733 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq792 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq769 eq744
    | exact resolve eq744 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq769 eq16
    | exact resolve eq16 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq798 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq792
  have eq799 : y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq791
  have eq802 : ∀ X0 : G, y = (M.op y x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq744 eq796
    | exact resolve eq796 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq796
  have eq811 : y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq565 x
       have i₂ := eq799
       grind)
    | exact superpose eq799 eq565
    | exact resolve eq565 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq815 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq799
       grind)
    | exact superpose eq799 eq16
    | exact resolve eq16 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq815 X0
       have i₂ := eq565 X0
       grind)
    | exact superpose eq565 eq815
    | exact resolve eq815 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq839 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq798 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq798
       grind)
    | exact resolve eq13 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq839 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq841 : ∀ X0 : G, y = (M.op y x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq802 eq840
    | exact resolve eq840 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq840
  have eq861 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq817 y
       have i₂ := eq811
       grind)
    | exact superpose eq811 eq817
    | exact resolve eq817 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq817
  have eq870 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq861
  have eq887 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq799
       have i₂ := eq870
       grind)
    | exact superpose eq870 eq799
    | exact resolve eq799 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq870
  have eq895 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq887
  have eq907 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq895 eq32
    | exact resolve eq32 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq895
  have eq940 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq907
    | exact resolve eq907 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq907
  have eq941 : x = y := by grind
  clear eq940
  have eq942 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq18
    | exact resolve eq18 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq24
    | exact resolve eq24 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq953 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq565 X0
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq565
    | exact resolve eq565 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq963 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq943
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq943
    | exact resolve eq943 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq964 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq963 eq26
    | exact resolve eq26 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq983 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq963 eq716
    | exact resolve eq716 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq963
  have eq988 : x = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq983
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq983
    | exact resolve eq983 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq999 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq988
       have i₂ := eq942
       grind)
    | exact superpose eq942 eq988
    | exact resolve eq988 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1010 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq964 eq798
    | exact resolve eq798 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq1014 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq964 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq964
  have eq1018 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1010
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq1010
    | exact resolve eq1010 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1020 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1018
       have i₂ := eq942
       grind)
    | exact superpose eq942 eq1018
    | exact resolve eq1018 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1022 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1020 eq27
    | exact resolve eq27 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1405 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq953 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq953
    | (have j0 := eq953 y
       grind)
    | exact resolve eq953 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq953
  have eq1863 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq841 X0
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq841
    | (have j0 := eq841 X0
       grind)
    | exact resolve eq841 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq1890 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1863 X0
       have i₂ := eq942
       grind)
    | exact superpose eq942 eq1863
    | (have j0 := eq1863 X0
       grind)
    | exact resolve eq1863 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq1863
  have eq1921 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1890 eq999
    | exact resolve eq999 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq1890
  have eq1928 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1921
  have eq1940 : x = (M.op x y) := by
    first
    | (have r₁ := eq1928
       have r₂ := eq1022
       grind)
    | exact resolve eq1928 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq1928
  have eq1962 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1940
       grind)
    | exact superpose eq1940 eq22
    | exact resolve eq22 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1986 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1405
       have i₂ := eq1940
       grind)
    | exact superpose eq1940 eq1405
    | exact resolve eq1405 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq2004 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1962 eq20
    | exact resolve eq20 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962
  have eq2075 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1986 eq181
    | exact resolve eq181 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2078 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1986 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq1986
       grind)
    | exact resolve eq13 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986
  have eq2085 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq2078 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078
  have eq2090 : y = (k y (M.op x y)) := by
    first
    | exact superpose eq2085 eq2075
    | exact resolve eq2075 eq2085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075 eq2085
  have eq2095 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq2090
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq2090
    | exact resolve eq2090 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq2090
  have eq2097 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2095
       have i₂ := eq1940
       grind)
    | exact superpose eq1940 eq2095
    | exact resolve eq2095 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940 eq2095
  have eq2100 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2097 eq38
    | exact resolve eq38 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2097
  have eq2107 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2100
    | exact resolve eq2100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2100
  have eq2109 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2004 eq2107
    | exact resolve eq2107 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107
  have eq2113 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2109 eq1014
    | exact resolve eq1014 eq2109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq2109
  have eq2122 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2113
  have eq2131 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2122 eq27
    | exact resolve eq27 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2122
  have eq2157 : False := by grind
  exact eq2157

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_y_pxy_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = b :=
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
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq57 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq83
    | exact resolve eq83 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq555 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq562 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq555 X0
       grind)
    | exact superpose eq555 eq14
    | exact resolve eq14 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq1047 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq56 eq562
    | exact resolve eq562 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1050 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq57 eq562
    | exact resolve eq562 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq8830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq8831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq8830
    | exact resolve eq8830 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8830
  have eq8842 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq8831
       have r₂ := eq28
       grind)
    | exact resolve eq8831 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8831
  have eq8848 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq8842 eq70
    | exact resolve eq70 eq8842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8842
  have eq8929 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq8848
    | exact resolve eq8848 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8848
  have eq8930 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8929
  have eq8941 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq8930
       grind)
    | exact superpose eq8930 eq52
    | exact resolve eq52 eq8930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq8948 : y = (M.op (M.op (M.op x y) x) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq8930
       grind)
    | exact superpose eq8930 eq53
    | exact resolve eq53 eq8930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq8949 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq8930
       grind)
    | exact superpose eq8930 eq56
    | exact resolve eq56 eq8930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq8930
  have eq9019 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1047 eq8949
    | exact resolve eq8949 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq8949
  have eq9026 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8941
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8941
    | exact resolve eq8941 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8941
  have eq9357 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9026 eq54
    | exact resolve eq54 eq9026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq9358 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9026 eq57
    | exact resolve eq57 eq9026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq9026
  have eq9426 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1050 eq9358
    | exact resolve eq9358 eq1050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050 eq9358
  have eq9606 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9019 eq8948
    | exact resolve eq8948 eq9019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8948 eq9019
  have eq9623 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9606
  have eq9624 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq9623
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9623
    | exact resolve eq9623 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9623
  have eq9626 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9624 eq30
    | exact resolve eq30 eq9624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9624
  have eq9745 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq9626
    | exact resolve eq9626 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9626
  have eq9746 : y = (M.op x y) ∨ x = y := by grind
  clear eq9745
  have eq9910 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq9746 eq21
    | exact resolve eq21 eq9746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9746
  have eq10041 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9910
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9910
    | exact resolve eq9910 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9910
  have eq28995 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9426 eq9357
    | exact resolve eq9357 eq9426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9357 eq9426
  have eq29030 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq28995
  have eq29031 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq29030
    | exact resolve eq29030 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29030
  have eq29343 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29031 eq28
    | exact resolve eq28 eq29031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29031
  have eq29382 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq29343
       have r₂ := eq10041
       grind)
    | exact resolve eq29343 eq10041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10041 eq29343
  have eq29385 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq29382 eq30
    | exact resolve eq30 eq29382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29382
  have eq29619 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq29385
    | exact resolve eq29385 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29385
  have eq29620 : x = y := by grind
  clear eq29619
  have eq29639 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq29620
       grind)
    | exact superpose eq29620 eq19
    | exact resolve eq19 eq29620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29640 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq29620
       grind)
    | exact superpose eq29620 eq25
    | exact resolve eq25 eq29620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29620
  have eq29770 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29640
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29640
    | exact resolve eq29640 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29640
  have eq30003 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29770 eq27
    | exact resolve eq27 eq29770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29770
  have eq30383 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq30003 eq70
    | exact resolve eq70 eq30003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq30003
  have eq30470 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq30383
       have i₂ := eq29639
       grind)
    | exact superpose eq29639 eq30383
    | exact resolve eq30383 eq29639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29639 eq30383
  have eq30480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30470 eq15
    | exact resolve eq15 eq30470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30470
  have eq30545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq30480
    | exact resolve eq30480 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq30480
  have eq30561 : False := by grind
  exact eq30561

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op X1 X0) X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq43
    | exact resolve eq43 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq43 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq45 (M.op X0 X0) X1
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (M.op X1 X1) X0
       have i₂ := eq48 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq48 eq45
    | exact resolve eq45 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq126 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq63
    | exact resolve eq63 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq128 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq54
    | exact resolve eq54 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq129 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq48
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq273 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 (σ (M.op X1 X1))
       have i₂ := eq126 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq126 eq129
    | exact resolve eq129 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq129
  have eq310 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq16
    | (have j1 := eq94 x (M.op x x)
       grind)
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq369 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq128 X1 X0
       grind)
    | exact superpose eq128 eq10
    | exact resolve eq10 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4317 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq310
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq310
    | (have j1 := eq14 (M.op x x) x
       grind)
    | (have r₁ := eq310
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq310
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq310 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq4318 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq4317
  have eq30664 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4318
       grind)
    | exact superpose eq4318 eq16
    | exact resolve eq16 eq4318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4318
  have eq30665 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq30664
       have r₂ := eq128 x (σ x)
       grind)
    | exact resolve eq30664 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30664
  have eq312662 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30665
       grind)
    | exact superpose eq30665 eq10
    | exact resolve eq10 eq30665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30665
  have eq312735 : x = y ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq312662
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq312662
    | exact resolve eq312662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312662
  have eq312737 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq312735
       grind)
    | exact superpose eq312735 eq16
    | exact resolve eq16 eq312735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312735
  have eq312738 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq312737
       have r₂ := eq128 x (σ x)
       grind)
    | exact resolve eq312737 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq312737
  have eq312894 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq312738
       grind)
    | exact superpose eq312738 eq10
    | exact resolve eq10 eq312738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312738
  have eq312983 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq312894
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq312894
    | exact resolve eq312894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312894
  have eq312984 : x = (M.op x x) := by grind
  clear eq312983
  have eq313695 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48 x X0
       have i₂ := eq312984
       grind)
    | exact superpose eq312984 eq48
    | exact resolve eq48 eq312984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq313713 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq273 x X0
       have i₂ := eq312984
       grind)
    | exact superpose eq312984 eq273
    | exact resolve eq273 eq312984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq313718 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq369 x X0
       have i₂ := eq312984
       grind)
    | exact superpose eq312984 eq369
    | exact resolve eq369 eq312984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq312984
  have eq314257 : (σ x) = (σ (τ x)) := by
    first
    | (have i₁ := eq313713 x
       have i₂ := eq313718 x
       grind)
    | exact superpose eq313718 eq313713
    | exact resolve eq313713 eq313718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313713 eq313718
  have eq314310 : x = (σ x) := by
    first
    | (have i₁ := eq314257
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq314257
    | exact resolve eq314257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314257
  have eq314350 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq314310
       grind)
    | exact superpose eq314310 eq16
    | exact resolve eq16 eq314310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314310
  have eq314431 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq314350
       have i₂ := eq313695 (σ y)
       grind)
    | exact superpose eq313695 eq314350
    | exact resolve eq314350 eq313695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314350
  have eq314454 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq314431
       have i₂ := eq313695 y
       grind)
    | exact superpose eq313695 eq314431
    | exact resolve eq314431 eq313695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313695 eq314431
  have eq314455 : False := by grind
  exact eq314455

/-- `Equation2936`: `x = ((y ◇ (y ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2936 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2936 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2936.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X1 X0)) X0) X0) = X0 := by
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
  have eq51 : (σ y) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op X1 (M.op X1 X0)) X0) X0) X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 (M.op X1 X0)) X0)
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x
       have i₂ := eq14 X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq36
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq72
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq72 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq110 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq111 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq112 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq112 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq43
    | exact resolve eq43 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq118 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq49
    | exact resolve eq49 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq121 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq118
    | exact resolve eq118 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq123 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq116
    | exact resolve eq116 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq116
  have eq841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq98 eq67
    | (have j0 := eq67 (σ y) (σ x)
       grind)
    | exact resolve eq67 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq841
    | exact resolve eq841 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq845 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq842
       have r₂ := eq27
       grind)
    | exact resolve eq842 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq847 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq845
    | exact resolve eq845 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq849 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq847 eq111
    | (have r₁ := eq111
       have r₂ := eq847
       grind)
    | exact resolve eq111 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq850 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq847 eq121
    | exact resolve eq121 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq857 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq849
  have eq867 : x = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq850
       grind)
    | exact superpose eq850 eq53
    | exact resolve eq53 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq857 eq98
    | exact resolve eq98 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq857
  have eq928 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq925
  have eq930 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq928
       have r₂ := eq27
       grind)
    | exact resolve eq928 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq933 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq930
       grind)
    | exact superpose eq930 eq110
    | (have r₁ := eq110
       have r₂ := eq930
       grind)
    | exact resolve eq110 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq930
       grind)
    | exact superpose eq930 eq123
    | exact resolve eq123 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq938 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq930
       grind)
    | exact superpose eq930 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq941 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq933
  have eq943 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq934
    | exact resolve eq934 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1060 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq72
    | exact resolve eq72 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq1062 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1060
    | exact resolve eq1060 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1062 eq67
    | (have j0 := eq67 (σ y) (σ x)
       grind)
    | exact resolve eq67 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1067
    | exact resolve eq1067 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1073 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1070
       have r₂ := eq27
       grind)
    | exact resolve eq1070 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1075 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1073
    | exact resolve eq1073 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1075 eq943
    | exact resolve eq943 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1130
  have eq1146 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1143
       have r₂ := eq27
       grind)
    | exact resolve eq1143 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1152 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1146 eq27
    | exact resolve eq27 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1380 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq938 X0
       grind)
    | (have r₁ := eq938 X0
       have r₂ := eq1146
       grind)
    | exact resolve eq938 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938 eq1146
  have eq1387 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1380 y
       grind)
    | exact superpose eq1380 eq72
    | exact resolve eq72 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq1406 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1387
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1387
    | exact resolve eq1387 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1408 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1406
    | exact resolve eq1406 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq1467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1408 eq67
    | (have j0 := eq67 (σ y) (σ x)
       grind)
    | exact resolve eq67 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq1470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1467
    | exact resolve eq1467 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1473 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1470
       have r₂ := eq27
       grind)
    | exact resolve eq1470 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1475 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1473
    | exact resolve eq1473 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1475 eq943
    | exact resolve eq943 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq1475
  have eq1498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1488
  have eq1503 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1498
       have r₂ := eq27
       grind)
    | exact resolve eq1498 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1562 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1503 eq27
    | exact resolve eq27 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (σ y)) := by
    first
    | exact superpose eq1503 eq51
    | exact resolve eq51 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1565 : x = (M.op (τ (σ x)) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1503 eq867
    | exact resolve eq867 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq1568 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq1565
    | exact resolve eq1565 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1684 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq847 eq1563
    | exact resolve eq1563 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq1687 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1503 eq1684
    | exact resolve eq1684 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1688 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq1687
    | exact resolve eq1687 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq1689 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1503 eq1688
    | exact resolve eq1688 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1690 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq1689
    | exact resolve eq1689 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1691 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1503 eq1690
    | exact resolve eq1690 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq1693 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq1691
       grind)
    | exact superpose eq1691 eq110
    | (have r₁ := eq110
       have r₂ := eq1691
       grind)
    | exact resolve eq110 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1694 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq123
       have i₂ := eq1691
       grind)
    | exact superpose eq1691 eq123
    | exact resolve eq123 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1701 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1693
  have eq1703 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq1694
    | exact resolve eq1694 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1981 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq123
       have i₂ := eq1568
       grind)
    | exact superpose eq1568 eq123
    | exact resolve eq123 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq1568
  have eq1992 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1981
    | exact resolve eq1981 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq2314 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1701
       grind)
    | exact superpose eq1701 eq72
    | exact resolve eq72 eq1701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1701
  have eq2317 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq2314
    | exact resolve eq2314 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314
  have eq2322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2317 eq67
    | (have j0 := eq67 (σ y) (σ x)
       grind)
    | exact resolve eq67 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2317
  have eq2323 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq2322
    | exact resolve eq2322 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2322
  have eq2326 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2323
       have r₂ := eq27
       grind)
    | exact resolve eq2323 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2323
  have eq2328 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq2326
    | exact resolve eq2326 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2326
  have eq2330 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1503 eq2328
    | exact resolve eq2328 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503 eq2328
  have eq2345 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2330 eq1703
    | exact resolve eq1703 eq2330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703 eq2330
  have eq2351 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2345
  have eq2360 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2351
       have r₂ := eq1152
       grind)
    | exact resolve eq2351 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152 eq2351
  have eq2379 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2360 eq29
    | exact resolve eq29 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2360
  have eq2409 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq2379
    | exact resolve eq2379 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2379
  have eq2473 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2409 eq20
    | exact resolve eq20 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2511 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2473
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2473
    | exact resolve eq2473 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq2514 : x = y := by
    first
    | (have r₁ := eq2511
       have r₂ := eq1562
       grind)
    | exact resolve eq2511 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq2515 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2514
       grind)
    | exact superpose eq2514 eq18
    | exact resolve eq18 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2516 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2514
       grind)
    | exact superpose eq2514 eq24
    | exact resolve eq24 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2514
  have eq2547 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2516
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2516
    | exact resolve eq2516 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2516
  have eq2569 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (σ x)) := by
    first
    | exact superpose eq2547 eq1563
    | exact resolve eq1563 eq2547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq2547
  have eq2570 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2569
       have i₂ := eq53 sF2
       grind)
    | exact superpose eq53 eq2569
    | exact resolve eq2569 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2569
  have eq2737 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2570 eq1992
    | exact resolve eq1992 eq2570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992 eq2570
  have eq2747 : x = (M.op x x) := by
    first
    | (have r₁ := eq2737
       have r₂ := eq1562
       grind)
    | exact resolve eq2737 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq2752 : x = (M.op x y) := by
    first
    | (have i₁ := eq2747
       have i₂ := eq2515
       grind)
    | exact superpose eq2515 eq2747
    | exact resolve eq2747 eq2515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515 eq2747
  have eq2755 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2752 eq20
    | exact resolve eq20 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2752
  have eq2797 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2755
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2755
    | exact resolve eq2755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2755
  have eq2804 : False := by grind
  exact eq2804

/-- `Equation3150`: `x = (((y ◇ y) ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation3150 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3150 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3150.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq91 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq154 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq16
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq593 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq629 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq593
    | (have j0 := eq593 X0 X1
       grind)
    | exact resolve eq593 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq742 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq157 (τ X1) (τ X0)
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq157
    | (have j0 := eq157 (τ X1) (τ X0)
       grind)
    | exact resolve eq157 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq751 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq742
    | (have j0 := eq742 X0 X1
       grind)
    | exact resolve eq742 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq754 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq751 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq751
    | (have j0 := eq751 X0 X1
       grind)
    | exact resolve eq751 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq756 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq754 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq754
    | (have j0 := eq754 X0 X1
       grind)
    | exact resolve eq754 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq757 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq756 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq756
    | (have j0 := eq756 X0 X1
       grind)
    | exact resolve eq756 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq758 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq757 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq757
    | (have j0 := eq757 X0 X1
       grind)
    | exact resolve eq757 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq759 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq758 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq758
    | (have j0 := eq758 X0 X1
       grind)
    | exact resolve eq758 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq851 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq154
       have i₂ := eq629 x y
       grind)
    | exact superpose eq629 eq154
    | (have j1 := eq629 (σ x) (σ y)
       grind)
    | (have r₁ := eq154
       have r₂ := eq629 x y
       grind)
    | (have r₁ := eq154
       have r₂ := eq629 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq154
       have r₂ := eq629 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq154 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq629
  have eq852 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq851
  have eq6047 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq16
    | exact resolve eq16 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq6048 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6047
       have r₂ := eq22 x
       grind)
    | exact resolve eq6047 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6047
  have eq6189 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6048
       grind)
    | exact superpose eq6048 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6048
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6048
       grind)
    | exact resolve eq13 eq6048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6048
  have eq6190 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6189
  have eq7961 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6190
       grind)
    | exact superpose eq6190 eq16
    | exact resolve eq16 eq6190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6190
  have eq7962 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7961
       have r₂ := eq22 x
       grind)
    | exact resolve eq7961 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7961
  have eq8061 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq157 x y
       have i₂ := eq7962
       grind)
    | exact superpose eq7962 eq157
    | (have j0 := eq157 x y
       grind)
    | exact resolve eq157 eq7962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq7962
  have eq8070 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8061
  have eq8071 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8070
  have eq8077 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8071
       grind)
    | exact superpose eq8071 eq16
    | exact resolve eq16 eq8071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8078 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq8071
       grind)
    | exact superpose eq8071 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8071
       grind)
    | exact resolve eq13 eq8071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8071
  have eq8079 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq8078
  have eq8080 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq8079
  have eq8082 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq8080
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8080
    | exact resolve eq8080 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8080
  have eq8198 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8082
       grind)
    | exact superpose eq8082 eq10
    | exact resolve eq10 eq8082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8082
  have eq8276 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq8198
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8198
    | exact resolve eq8198 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8198
  have eq8477 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8276
       grind)
    | exact superpose eq8276 eq16
    | exact resolve eq16 eq8276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8276
  have eq8478 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq8477
       have r₂ := eq22 x
       grind)
    | exact resolve eq8477 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8477
  have eq8488 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq8478
       grind)
    | exact superpose eq8478 eq10
    | exact resolve eq10 eq8478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8478
  have eq8568 : y = (k y x) := by
    first
    | (have i₁ := eq8488
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8488
    | exact resolve eq8488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8488
  have eq8694 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq759 y x
       have i₂ := eq8568
       grind)
    | exact superpose eq8568 eq759
    | (have j0 := eq759 y x
       grind)
    | (have r₁ := eq759 y x
       have r₂ := eq8568
       grind)
    | exact resolve eq759 eq8568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759 eq8568
  have eq8700 : x = y ∨ y = (M.op x y) := by grind
  clear eq8694
  have eq8705 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8700
       grind)
    | exact superpose eq8700 eq16
    | exact resolve eq16 eq8700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8700
  have eq8710 : y = (M.op x y) := by
    first
    | (have r₁ := eq8705
       have r₂ := eq22 x
       grind)
    | exact resolve eq8705 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8705
  have eq8884 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8077
       have i₂ := eq8710
       grind)
    | exact superpose eq8710 eq8077
    | exact resolve eq8077 eq8710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8077 eq8710
  have eq8887 : (σ x) = (σ y) := by grind
  clear eq8884
  have eq8889 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8887
       grind)
    | exact superpose eq8887 eq10
    | exact resolve eq10 eq8887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8887
  have eq8968 : x = y := by
    first
    | (have i₁ := eq8889
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8889
    | exact resolve eq8889 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8889
  have eq9000 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8968
       grind)
    | exact superpose eq8968 eq16
    | exact resolve eq16 eq8968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8968
  have eq9006 : False := by grind
  exact eq9006
