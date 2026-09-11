import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyy_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq81 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) x
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq86 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1
       have i₂ := eq81 X0 x
       grind)
    | exact superpose eq81 eq9
    | exact resolve eq9 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq58 x
       have i₂ := eq81 sF2 x
       grind)
    | exact superpose eq81 eq58
    | exact resolve eq58 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq108 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq119 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (M.op X0 X1) x
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq92 (M.op x y) X0
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq92
    | exact resolve eq92 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 sF0 X1
       have i₂ := eq9 sF0 x x
       grind)
    | (have i₁ := eq119 x X1
       have i₂ := eq9 x sF0 x
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq139 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 X1
       have i₂ := eq81 sF0 x
       grind)
    | exact superpose eq81 eq134
    | exact resolve eq134 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq149 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq150 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq61 eq150
    | exact resolve eq150 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq199 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq153 (σ X0)
       grind)
    | exact superpose eq153 eq15
    | exact resolve eq15 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq199 X0
       have i₂ := eq153 X0
       grind)
    | exact superpose eq153 eq199
    | exact resolve eq199 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq199
  have eq216 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 (M.op X0 X1) x
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq108 (M.op x y) X0
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq108
    | exact resolve eq108 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) (σ x)) := by
    first
    | exact superpose eq94 eq108
    | exact resolve eq108 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq222
       have i₂ := eq57 sF0 sF2 sF2
       grind)
    | exact superpose eq57 eq222
    | exact resolve eq222 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq238 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq108 eq216
    | exact resolve eq216 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq242 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq108 eq234
    | exact resolve eq234 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq259 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq242 eq9
    | exact resolve eq9 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq238 eq12
    | (have j0 := eq12 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (M.op x y) (M.op (σ x) (σ y))
       have r₂ := eq238 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq302 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       grind)
    | (have r₁ := eq297 X0 X1
       have r₂ := eq242
       grind)
    | exact resolve eq297 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq303 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq242 eq302
    | exact resolve eq302 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq323 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq303 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq303
    | (have j0 := eq303 x y
       grind)
    | exact resolve eq303 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq342 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq415 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq424 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq415
    | exact resolve eq415 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq426 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq424
    | exact resolve eq424 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq428 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq426
    | exact resolve eq426 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq458 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op (σ x) (σ y)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq108 eq52
    | exact resolve eq52 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op x y) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq94 eq52
    | exact resolve eq52 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq493 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq52 X0 X0 X2 X1
       grind)
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq52 X0 X1 X2 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op X0 X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 X4
       have i₂ := eq52 X0 X2 (M.op X0 X2) X1
       grind)
    | (have i₁ := eq9 (M.op X0 X2) X3 X4
       have i₂ := eq52 X0 X1 (M.op X0 X2) X2
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 x
       have i₂ := eq57 sF0 sF2 x
       grind)
    | exact superpose eq57 eq465
    | exact resolve eq465 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq520 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X3) = (M.op (M.op X3 X4) (M.op X0 X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq500 X0 x X2 X3 X4
       have i₂ := eq458 X0 x (M.op X0 X2) X3
       grind)
    | (have i₁ := eq500 (σ x) (σ y) X2 X3 X4
       have i₂ := eq458 (M.op (σ x) X2) x X2 X3
       grind)
    | exact superpose eq458 eq500
    | exact resolve eq500 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq500
  have eq542 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq514 eq259
    | exact resolve eq259 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq544 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op X0 X2)) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X0 X2 X3 X4
    first
    | exact superpose eq514 eq520
    | exact resolve eq520 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514 eq520
  have eq565 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq200 (M.op x X0)
       have i₂ := eq81 (M.op x X0) X0
       grind)
    | (have i₁ := eq200 (M.op x y)
       have i₂ := eq81 (M.op x y) x
       grind)
    | exact superpose eq81 eq200
    | exact resolve eq200 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq200 X0
       grind)
    | exact superpose eq200 eq10
    | exact resolve eq10 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq139 eq565
    | exact resolve eq565 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq565
  have eq583 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq580 X0
       have i₂ := eq200 sF0
       grind)
    | exact superpose eq200 eq580
    | exact resolve eq580 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq585 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq20 eq583
    | (have j0 := eq583 X0
       grind)
    | exact resolve eq583 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq587 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq342 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq342
    | exact resolve eq342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq620 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq568 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq568
    | exact resolve eq568 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq660 : (τ (M.op (M.op (σ x) (σ y)) (M.op x y))) = (k (τ (M.op x y)) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq323 eq587
    | exact resolve eq587 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq587
  have eq701 : (τ (M.op (M.op (σ x) (σ y)) (M.op x y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq242 eq620
    | exact resolve eq620 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq706 : (k (τ (M.op x y)) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq660 eq701
    | exact resolve eq701 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq710 : (τ (M.op (M.op (σ x) (σ y)) (M.op x y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq706 eq660
    | exact resolve eq660 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq706
  have eq1299 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq542 eq52
    | exact resolve eq52 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq2405 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq200 (M.op X0 X0)
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq200
    | exact resolve eq200 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2523 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (σ (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2405 X0
       have i₂ := eq200 X0
       grind)
    | exact superpose eq200 eq2405
    | exact resolve eq2405 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2587 : ∀ X0 : G, (σ (M.op (M.op (M.op x y) X0) X0)) = (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2523 X0
       have i₂ := eq544 (σ X0) (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq544 eq2523
    | exact resolve eq2523 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523
  have eq4262 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) = (τ (M.op (M.op (M.op x y) (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq620 (M.op X0 X1)
       have i₂ := eq544 X0 X1 X0 X1
       grind)
    | (have i₁ := eq620 (M.op (M.op x y) (M.op x y))
       have i₂ := eq544 X0 x (M.op (M.op x y) (M.op x y)) x
       grind)
    | exact superpose eq544 eq620
    | exact resolve eq620 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4306 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op x y) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq544 eq52
    | exact resolve eq52 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5444 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq585 x
       have i₂ := eq200 x
       grind)
    | exact superpose eq200 eq585
    | exact resolve eq585 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq5507 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq5444
       have i₂ := eq544 (σ x) (σ x) (σ x) (σ x)
       grind)
    | exact superpose eq544 eq5444
    | exact resolve eq5444 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq5444
  have eq5522 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5507
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5507
    | exact resolve eq5507 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5507
  have eq5528 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq108 eq5522
    | exact resolve eq5522 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5522
  have eq5539 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5528 eq710
    | exact resolve eq710 eq5528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq5528
  have eq5564 : (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq5539
       have i₂ := eq620 sF1
       grind)
    | exact superpose eq620 eq5539
    | exact resolve eq5539 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5539
  have eq5570 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq37 eq5564
    | exact resolve eq5564 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq5564
  have eq6320 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op X0 X1) (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq5570 eq493
    | exact resolve eq493 eq5570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11432 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq6320 eq1299
    | exact resolve eq1299 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq11439 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X2) X0) = (M.op (M.op X0 X1) (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq6320 eq52
    | exact resolve eq52 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq6320
  have eq24853 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) = (σ (M.op (M.op X0 X1) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2587 x
       have i₂ := eq493 sF0 x x x
       grind)
    | (have i₁ := eq2587 X0
       have i₂ := eq493 X0 X1 sF0 X0
       grind)
    | exact superpose eq493 eq2587
    | exact resolve eq2587 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq24892 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) X0) = (τ (M.op (M.op (M.op x y) (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq2587 eq10
    | exact resolve eq10 eq2587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq33279 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (M.op x y) X0) X1)) = (M.op (τ (M.op X1 X2)) (τ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq620 (M.op X1 X2)
       have i₂ := eq4306 X1 X2 X1 X2 X0
       grind)
    | (have i₁ := eq620 (M.op (M.op x y) x)
       have i₂ := eq4306 (M.op (M.op x y) x) X1 X2 x x
       grind)
    | exact superpose eq4306 eq620
    | exact resolve eq620 eq4306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq4306
  have eq40935 : ∀ X0 : G, (τ (M.op (M.op (M.op x y) (M.op x y)) X0)) = (M.op (M.op (M.op x y) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq24892 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24892
    | exact resolve eq24892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24892
  have eq41026 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) (τ X0)) = (τ (M.op (M.op (M.op x y) (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq40935 X0
       have i₂ := eq57 sF0 (τ X0) (τ X0)
       grind)
    | exact superpose eq57 eq40935
    | exact resolve eq40935 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq40935
  have eq41058 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) = (M.op (M.op (M.op x y) (M.op x y)) (τ X0)) := by
    intro X0 X1
    first
    | exact superpose eq41026 eq4262
    | exact resolve eq4262 eq41026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4262 eq41026
  have eq41106 : ∀ X0 X1 : G, (τ (M.op (M.op (M.op x y) X0) X1)) = (M.op (M.op (M.op x y) (M.op x y)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33279 X0 X1 x
       have i₂ := eq41058 X1 x
       grind)
    | exact superpose eq41058 eq33279
    | exact resolve eq33279 eq41058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33279 eq41058
  have eq82414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq428
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq428
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq428 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq82414
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82414
    | exact resolve eq82414 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82414
  have eq82446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq82442
    | exact resolve eq82442 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82442
  have eq82448 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq82446
       have r₂ := eq27
       grind)
    | exact resolve eq82446 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82446
  have eq82449 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq82448
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82448
    | exact resolve eq82448 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82448
  have eq82450 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq82449
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82449
    | exact resolve eq82449 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82449
  have eq82451 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq82450 eq159
    | (have r₁ := eq159
       have r₂ := eq82450
       grind)
    | exact resolve eq159 eq82450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq82450
  have eq82589 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq82451
  have eq82784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq82589
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq82589
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq82589 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82589
  have eq82812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq82784
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82784
    | exact resolve eq82784 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82784
  have eq82816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq82812
    | exact resolve eq82812 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82812
  have eq82818 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq82816
       have r₂ := eq27
       grind)
    | exact resolve eq82816 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82816
  have eq82819 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq82818
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82818
    | exact resolve eq82818 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82818
  have eq82820 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq82819
  have eq82821 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq82820
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82820
    | exact resolve eq82820 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82820
  have eq82822 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq82821
  have eq82823 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq149
       have i₂ := eq82822
       grind)
    | exact superpose eq82822 eq149
    | (have r₁ := eq149
       have r₂ := eq82822
       grind)
    | exact resolve eq149 eq82822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq82842 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq200 x
       have i₂ := eq82822
       grind)
    | exact superpose eq82822 eq200
    | exact resolve eq200 eq82822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq82822
  have eq82964 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq82823
  have eq83039 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq82842
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq82842
    | exact resolve eq82842 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82842
  have eq83078 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq83039
    | exact resolve eq83039 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83039
  have eq83090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq428
       have i₂ := eq82964
       grind)
    | exact superpose eq82964 eq428
    | exact resolve eq428 eq82964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq82964
  have eq83095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq83090
  have eq83099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq83095
    | exact resolve eq83095 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83095
  have eq83102 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq83099
       have r₂ := eq27
       grind)
    | exact resolve eq83099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83099
  have eq83835 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq83102 eq83078
    | exact resolve eq83078 eq83102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83078 eq83102
  have eq83976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq83835
  have eq84066 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq83976
       have r₂ := eq27
       grind)
    | exact resolve eq83976 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83976
  have eq84152 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq84066 eq5570
    | exact resolve eq5570 eq84066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5570
  have eq84176 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 X2) (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq84066 eq11432
    | exact resolve eq11432 eq84066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11432
  have eq84177 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X1 X2) (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq84066 eq11439
    | exact resolve eq11439 eq84066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11439
  have eq84254 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X1 X2) x) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq38 eq84177
    | exact resolve eq84177 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84177
  have eq84255 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 X2) x) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq38 eq84176
    | exact resolve eq84176 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84176
  have eq84276 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq84152
    | exact resolve eq84152 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84152
  have eq84293 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq84254 X0 X1 x
       have i₂ := eq92 X1 x
       grind)
    | (have i₁ := eq84254 X0 x y
       have i₂ := eq92 x X1
       grind)
    | exact superpose eq92 eq84254
    | exact resolve eq84254 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84254
  have eq84294 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq84255 X0 X1 x
       have i₂ := eq92 X0 x
       grind)
    | (have i₁ := eq84255 x X1 y
       have i₂ := eq92 x X1
       grind)
    | exact superpose eq92 eq84255
    | exact resolve eq84255 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84255
  have eq84301 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq108 eq84294
    | exact resolve eq84294 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq84294
  have eq86916 : ∀ X0 : G, (M.op (M.op x x) (τ X0)) = (τ (M.op (M.op x x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq84276 eq41106
    | exact resolve eq41106 eq84276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41106 eq84276
  have eq87163 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (M.op (M.op x x) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq86916 X0
       have i₂ := eq81 X0 x
       grind)
    | exact superpose eq81 eq86916
    | exact resolve eq86916 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86916
  have eq87271 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (M.op (M.op x y) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq87163 X0
       have i₂ := eq81 (τ X0) x
       grind)
    | exact superpose eq81 eq87163
    | exact resolve eq87163 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87163
  have eq87350 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq84066 eq84301
    | exact resolve eq84301 eq84066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84301
  have eq87532 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq87350 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87350
  have eq88904 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87532 eq26
    | (have j1 := eq87532 (σ y)
       grind)
    | exact resolve eq26 eq87532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87532
  have eq374839 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88904 eq87271
    | exact resolve eq87271 eq88904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87271 eq88904
  have eq374977 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (σ y))) ∨ x = (M.op x y) := by grind
  clear eq374839
  have eq375043 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq374977
    | exact resolve eq374977 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq374977
  have eq375285 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq84066 eq375043
    | exact resolve eq375043 eq84066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84066 eq375043
  have eq375399 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq375285
  have eq375431 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq375399
    | exact resolve eq375399 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq375399
  have eq375469 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq375431 eq84293
    | exact resolve eq84293 eq375431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84293
  have eq375625 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq375469 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375469
  have eq384301 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq375625 eq375431
    | exact resolve eq375431 eq375625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375431 eq375625
  have eq384641 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq384301
  have eq384905 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq384641
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq384641
    | exact resolve eq384641 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384641
  have eq384906 : x = (M.op x y) := by grind
  clear eq384905
  have eq385096 : x = (M.op x y) := by
    first
    | exact superpose eq384906 eq18
    | exact resolve eq18 eq384906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq385097 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq384906 eq20
    | exact resolve eq20 eq384906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq385105 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq384906 eq81
    | exact resolve eq81 eq384906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq385106 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | exact superpose eq384906 eq92
    | exact resolve eq92 eq384906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq385664 : ∀ X0 X1 : G, (M.op (M.op x x) (σ X0)) = (σ (M.op (M.op X0 X1) x)) := by
    intro X0 X1
    first
    | exact superpose eq384906 eq24853
    | exact resolve eq24853 eq384906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24853 eq384906
  have eq394116 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op x x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq385664 X0 x
       have i₂ := eq385106 X0 x
       grind)
    | exact superpose eq385106 eq385664
    | exact resolve eq385664 eq385106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385106 eq385664
  have eq395340 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq385097
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq385097
    | exact resolve eq385097 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385097
  have eq397059 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq394116 X0
       have i₂ := eq385105 (σ X0) x
       grind)
    | exact superpose eq385105 eq394116
    | exact resolve eq394116 eq385105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394116
  have eq397624 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq395340 eq22
    | exact resolve eq22 eq395340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq397625 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq395340 eq26
    | exact resolve eq26 eq395340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq395340
  have eq419641 : (σ x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq397059 y
       have i₂ := eq385096
       grind)
    | exact superpose eq385096 eq397059
    | exact resolve eq397059 eq385096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385096 eq397059
  have eq419792 : (σ x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq419641
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq419641
    | exact resolve eq419641 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq419641
  have eq419827 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq419792
       have i₂ := eq397624
       grind)
    | exact superpose eq397624 eq419792
    | exact resolve eq419792 eq397624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397624 eq419792
  have eq420110 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq419827 eq385105
    | exact resolve eq385105 eq419827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385105
  have eq420336 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq420110 eq397625
    | exact resolve eq397625 eq420110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397625 eq420110
  have eq420362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq419827 eq420336
    | exact resolve eq420336 eq419827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419827 eq420336
  have eq420543 : False := by grind
  exact eq420543

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  clear eq44
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X0 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X2 X0 X2
       have i₂ := eq14 X0 X2 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
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
  have eq55 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 X2) X0
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X3) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : x ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq79 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq81 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq83 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq81 (σ X0)
       grind)
    | exact superpose eq81 eq10
    | exact resolve eq10 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq81 sF2
       grind)
    | exact superpose eq81 eq50
    | exact resolve eq50 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq85
       have i₂ := eq81 x
       grind)
    | exact superpose eq81 eq85
    | exact resolve eq85 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq83
    | exact resolve eq83 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq94 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq81 sF3
       grind)
    | exact superpose eq81 eq79
    | exact resolve eq79 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq81 y
       grind)
    | exact superpose eq81 eq95
    | exact resolve eq95 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq108
    | exact resolve eq108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq109
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq109
    | exact resolve eq109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq121 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq81 sF1
       grind)
    | exact superpose eq81 eq137
    | exact resolve eq137 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq81 sF0
       grind)
    | exact superpose eq81 eq140
    | exact resolve eq140 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq163 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq54 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0
       have i₂ := eq14 X0 sF2 x
       grind)
    | (have i₁ := eq55 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq81 (τ X0)
       grind)
    | exact superpose eq81 eq35
    | exact resolve eq35 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq358 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq347 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq347
    | exact resolve eq347 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq360 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq358 X0
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq358
    | exact resolve eq358 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq404 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq236 x X0
       have i₂ := eq14 x X0 X1
       grind)
    | (have i₁ := eq236 x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq236
    | exact resolve eq236 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq55 eq236
    | exact resolve eq236 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op x X0)
       have i₂ := eq236 X0 (M.op x X0)
       grind)
    | (have i₁ := eq54 (M.op x y)
       have i₂ := eq236 X0 (M.op x y)
       grind)
    | exact superpose eq236 eq54
    | exact resolve eq54 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq411 X0
       have i₂ := eq14 x sF0 (M.op x X0)
       grind)
    | exact superpose eq14 eq411
    | exact resolve eq411 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq417 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq415 X0
       have i₂ := eq236 x sF0
       grind)
    | exact superpose eq236 eq415
    | exact resolve eq415 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq428 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq244 eq55
    | exact resolve eq55 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq428 X0
       have i₂ := eq14 sF2 sF4 (M.op sF2 X0)
       grind)
    | exact superpose eq14 eq428
    | exact resolve eq428 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq436 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq244 eq434
    | exact resolve eq434 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq441 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (k X1 (τ X0))
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq88
    | exact resolve eq88 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq88
  have eq547 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) x) := by
    first
    | exact superpose eq406 eq404
    | exact resolve eq404 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq547
       have i₂ := eq14 x sF0 sF2
       grind)
    | exact superpose eq14 eq547
    | exact resolve eq547 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq564 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq556
       have i₂ := eq236 x sF0
       grind)
    | exact superpose eq236 eq556
    | exact resolve eq556 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq575 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X2 X2) X0 X3 X4
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq52 (M.op X1 X2) X0 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0) x X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq633 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X3 X3) (M.op X0 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X3 (M.op X0 X4) X2
       have i₂ := eq52 X0 X4 X2 X1
       grind)
    | (have i₁ := eq14 X3 (M.op X0 X4) X2
       have i₂ := eq52 X0 X1 X2 X4
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq595 (M.op X0 X0) x
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq595
    | exact resolve eq595 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) (σ x)) := by
    first
    | exact superpose eq406 eq595
    | exact resolve eq595 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq595 eq676
    | exact resolve eq676 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq699 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq595 eq667
    | exact resolve eq667 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq761 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op X3 X4) X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X3 X4 X2 X0
       have i₂ := eq52 X0 X0 (M.op X2 X2) X1
       grind)
    | (have i₁ := eq56 X3 X4 X2 X0
       have i₂ := eq52 X0 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq858 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq693 eq436
    | exact resolve eq436 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq693
  have eq893 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X4 X4) X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 X4 X2 X0 X3
       have i₂ := eq52 X0 X0 (M.op X2 X3) X1
       grind)
    | (have i₁ := eq57 X4 X2 X0 X3
       have i₂ := eq52 X0 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq52 eq57
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq57
  have eq1600 : (σ (M.op (k x x) (k x x))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq50 eq360
    | exact resolve eq360 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq360
  have eq1621 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq1600
       have i₂ := eq81 sF2
       grind)
    | exact superpose eq81 eq1600
    | exact resolve eq1600 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1623 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1621
       have i₂ := eq81 x
       grind)
    | exact superpose eq81 eq1621
    | exact resolve eq1621 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621
  have eq1625 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq244 eq1623
    | exact resolve eq1623 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1627 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | exact superpose eq699 eq1625
    | exact resolve eq1625 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq1625
  have eq1629 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (σ (M.op (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq1627
       have i₂ := eq236 x (M.op x x)
       grind)
    | exact superpose eq236 eq1627
    | exact resolve eq1627 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq1631 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq417 eq1629
    | exact resolve eq1629 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq1629
  have eq1632 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq142 eq1631
    | exact resolve eq1631 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1631
  have eq2451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2451
    | exact resolve eq2451 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451
  have eq2455 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2452
       have r₂ := eq28
       grind)
    | exact resolve eq2452 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2452
  have eq2457 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2455
    | exact resolve eq2455 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq2460 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2457 eq69
    | (have r₁ := eq69
       have r₂ := eq2457
       grind)
    | exact resolve eq69 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2461 : (M.op (M.op x y) (σ x)) = (M.op (σ x) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2457 eq406
    | exact resolve eq406 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2463 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2457 eq564
    | exact resolve eq564 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq2466 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2457 eq858
    | exact resolve eq858 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq2468 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2457 eq1632
    | exact resolve eq1632 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2475 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2460
  have eq2636 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2461 eq595
    | exact resolve eq595 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461
  have eq2638 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq595 eq2636
    | exact resolve eq2636 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2636
  have eq2646 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1632 eq2638
    | exact resolve eq2638 eq1632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq2718 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2468 eq244
    | exact resolve eq244 eq2468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq2747 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2475 eq110
    | exact resolve eq110 eq2475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq2475
  have eq2751 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2747
  have eq2943 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq2751 eq14
    | exact resolve eq14 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751
  have eq3617 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2457 eq2646
    | exact resolve eq2646 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq3632 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3617
  have eq3968 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3632 eq86
    | exact resolve eq86 eq3632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3632
  have eq4028 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq163 eq3968
    | exact resolve eq3968 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968
  have eq4119 : (M.op (M.op x x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4028 eq595
    | exact resolve eq595 eq4028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4121 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1632 eq4119
    | exact resolve eq4119 eq1632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632 eq4119
  have eq4149 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq595 eq4121
    | exact resolve eq4121 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4121
  have eq4161 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq406 eq4149
    | exact resolve eq4149 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq4149
  have eq4260 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (M.op x y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4161 eq163
    | exact resolve eq163 eq4161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq5025 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2463 eq4260
    | exact resolve eq4260 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4260
  have eq5042 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq5025
  have eq9343 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq575 X0 X1 X2 X3 x
       have i₂ := eq579 X2 X3 x
       grind)
    | exact superpose eq579 eq575
    | exact resolve eq575 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq579
  have eq10593 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op X0 X4)) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq633 X0 x X2 X3 X4
       have i₂ := eq9343 X0 x X2 X3
       grind)
    | (have i₁ := eq633 x y X2 X3 X4
       have i₂ := eq9343 X0 x X2 X3
       grind)
    | exact superpose eq9343 eq633
    | exact resolve eq633 eq9343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq11613 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq761 X0 X1 X2 x x
       have i₂ := eq9343 x x X2 X0
       grind)
    | (have i₁ := eq761 x X1 X2 x y
       have i₂ := eq9343 X0 X1 X2 x
       grind)
    | exact superpose eq9343 eq761
    | (have j0 := eq761 X0 X1 X2 x y
       grind)
    | exact resolve eq761 eq9343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq12435 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2468 eq2466
    | exact resolve eq2466 eq2468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466 eq2468
  have eq12483 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12435
  have eq14846 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq893 X0 X1 X2 X3 x
       have i₂ := eq9343 x x X2 X0
       grind)
    | exact superpose eq9343 eq893
    | exact resolve eq893 eq9343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq9343
  have eq15067 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2943 eq2718
    | exact resolve eq2718 eq2943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718 eq2943
  have eq15094 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq15067
  have eq16228 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2457 eq15094
    | exact resolve eq15094 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15094
  have eq16273 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16228
  have eq16287 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq16273
    | exact resolve eq16273 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16273
  have eq16306 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16287 eq4161
    | exact resolve eq4161 eq16287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4161
  have eq16313 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16287 eq12483
    | exact resolve eq12483 eq16287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12483 eq16287
  have eq16369 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16313
  have eq16376 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16306
  have eq16505 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2457 eq16369
    | exact resolve eq16369 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16369
  have eq16545 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16505
  have eq16568 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16376 eq2463
    | exact resolve eq2463 eq16376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463 eq16376
  have eq16610 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16568
  have eq16702 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16545 eq86
    | exact resolve eq86 eq16545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16545
  have eq16821 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq16702
    | exact resolve eq16702 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16702
  have eq16846 : (M.op (σ x) (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16610 eq4028
    | exact resolve eq4028 eq16610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028
  have eq16848 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16610 eq5042
    | exact resolve eq5042 eq16610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042 eq16610
  have eq16916 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16848
  have eq16918 : (M.op (σ x) (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16846
  have eq16955 : (σ x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2457 eq16916
    | exact resolve eq16916 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457 eq16916
  have eq16992 : (σ x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16955
  have eq16995 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq16992
    | exact resolve eq16992 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16992
  have eq17001 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16995 eq30
    | exact resolve eq30 eq16995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16995
  have eq17019 : x = y ∨ x = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq17001
    | exact resolve eq17001 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17001
  have eq17020 : x = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq17019
  have eq17037 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq17020 eq595
    | exact resolve eq595 eq17020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq17173 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17037 X0 x
       have i₂ := eq404 X0 x
       grind)
    | (have i₁ := eq17037 x y
       have i₂ := eq404 x x
       grind)
    | exact superpose eq404 eq17037
    | exact resolve eq17037 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq17037
  have eq18805 : x = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16821
       have i₂ := eq16918
       grind)
    | exact superpose eq16918 eq16821
    | exact resolve eq16821 eq16918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16918
  have eq18867 : (σ x) = (σ y) ∨ x = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq18805
  have eq19387 : y = (τ (σ x)) ∨ x = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18867 eq30
    | exact resolve eq30 eq18867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18867
  have eq19412 : x = y ∨ x = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq19387
    | exact resolve eq19387 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19387
  have eq19413 : x = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq19412
  have eq19418 : x ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq19413 eq69
    | exact resolve eq69 eq19413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq19463 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19413 eq17173
    | exact resolve eq17173 eq19413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17173 eq19413
  have eq19464 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19463 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19463
  have eq19500 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19418
       have r₂ := eq17020
       grind)
    | exact resolve eq19418 eq17020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17020 eq19418
  have eq20100 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq19500 eq94
    | exact resolve eq94 eq19500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq19500
  have eq20110 : (M.op y y) = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq121 eq20100
    | exact resolve eq20100 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq20100
  have eq20113 : (M.op y y) = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq20110
       have r₂ := eq68
       grind)
    | exact resolve eq20110 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq20110
  have eq20117 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq20113
       grind)
    | exact superpose eq20113 eq11
    | (have j0 := eq11 (M.op x y) (M.op y y)
       grind)
    | exact resolve eq11 eq20113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20113
  have eq20118 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq20117
  have eq20120 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20118
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20118
    | exact resolve eq20118 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20118
  have eq20123 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq20120
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20120
    | exact resolve eq20120 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20120
  have eq20335 : (M.op (M.op x y) x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq20123
       grind)
    | exact superpose eq20123 eq54
    | exact resolve eq54 eq20123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq20123
  have eq24201 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20335 eq19464
    | exact resolve eq19464 eq20335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20335
  have eq24230 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq24201
  have eq24244 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24230
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24230
    | exact resolve eq24230 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24230
  have eq24270 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq24244 eq19464
    | exact resolve eq19464 eq24244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19464 eq24244
  have eq24295 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq24270
  have eq24332 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16821
       have i₂ := eq24295
       grind)
    | exact superpose eq24295 eq16821
    | exact resolve eq16821 eq24295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16821 eq24295
  have eq24388 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq24332
  have eq24447 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24388 eq30
    | exact resolve eq30 eq24388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24388
  have eq24484 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq24447
    | exact resolve eq24447 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq24447
  have eq24485 : x = (M.op x y) ∨ x = y := by grind
  clear eq24484
  have eq24488 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq24485 eq21
    | exact resolve eq21 eq24485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24520 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x X3) X0) = (M.op (M.op X0 X0) (M.op X1 X2)) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq24485 eq10593
    | exact resolve eq10593 eq24485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10593
  have eq24525 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op x X3) X0) ∨ x = y := by
    intro X0 X1 X3
    first
    | (have i₁ := eq24520 X0 X1 x X3
       have i₂ := eq14846 X0 X0 X1 x
       grind)
    | (have i₁ := eq24520 (M.op x y) X1 x X3
       have i₂ := eq14846 (M.op X1 x) X1 (M.op x y) X3
       grind)
    | exact superpose eq14846 eq24520
    | exact resolve eq24520 eq14846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14846 eq24520
  have eq24541 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq24488
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24488
    | exact resolve eq24488 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24488
  have eq24542 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X1) X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq24525 X0 X1 x
       have i₂ := eq236 x X0
       grind)
    | (have i₁ := eq24525 X1 X1 y
       have i₂ := eq236 X0 X1
       grind)
    | exact superpose eq236 eq24525
    | (have j0 := eq24525 X0 X1 y
       grind)
    | exact resolve eq24525 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24525
  have eq24548 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24541 eq27
    | exact resolve eq27 eq24541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24541
  have eq34583 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq24485 eq24542
    | exact resolve eq24542 eq24485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34876 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq34583 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34583
  have eq34968 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq34876 X0 x
       have i₂ := eq236 x X0
       grind)
    | (have i₁ := eq34876 x y
       have i₂ := eq236 X0 x
       grind)
    | exact superpose eq236 eq34876
    | (have j0 := eq34876 X0 y
       grind)
    | exact resolve eq34876 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34876
  have eq36924 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (k (σ (τ X0)) X0) (k (σ (τ X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq441 (τ x) x
       have i₂ := eq81 (τ x)
       grind)
    | exact superpose eq81 eq441
    | exact resolve eq441 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq36984 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36924 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36924
    | exact resolve eq36924 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36924
  have eq37007 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq36984 x
       have i₂ := eq81 x
       grind)
    | exact superpose eq81 eq36984
    | exact resolve eq36984 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq36984
  have eq37011 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (M.op x y) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37007 X0
       have i₂ := eq11613 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq11613 eq37007
    | exact resolve eq37007 eq11613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37007
  have eq37013 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) X0) = (σ (M.op (M.op (M.op x y) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37011 X0
       have i₂ := eq11613 X0 X0 X0
       grind)
    | exact superpose eq11613 eq37011
    | exact resolve eq37011 eq11613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11613 eq37011
  have eq141898 : ∀ X0 : G, (M.op (M.op x X0) X0) = (σ (M.op (M.op x (τ X0)) (τ X0))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq24485 eq37013
    | exact resolve eq37013 eq24485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24485 eq37013
  have eq142231 : ∀ X0 : G, (σ (M.op (M.op x y) (τ X0))) = (M.op (M.op x X0) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq141898 X0
       have i₂ := eq236 (τ X0) (τ X0)
       grind)
    | exact superpose eq236 eq141898
    | exact resolve eq141898 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141898
  have eq142315 : ∀ X0 : G, (M.op (M.op x y) X0) = (σ (M.op (M.op x y) (τ X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq142231 X0
       have i₂ := eq236 X0 X0
       grind)
    | (have i₁ := eq142231 y
       have i₂ := eq236 X0 y
       grind)
    | exact superpose eq236 eq142231
    | exact resolve eq142231 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq142231
  have eq142474 : (σ (M.op (M.op x y) y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30 eq142315
    | exact resolve eq142315 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq142315
  have eq142894 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq34968 eq142474
    | exact resolve eq142474 eq34968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34968 eq142474
  have eq142978 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by grind
  clear eq142894
  have eq142993 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq142978
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq142978
    | exact resolve eq142978 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142978
  have eq143002 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq142993
    | exact resolve eq142993 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142993
  have eq143034 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq143002 eq24542
    | exact resolve eq24542 eq143002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24542
  have eq143126 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq143034 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143034
  have eq146054 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq143126 eq24548
    | exact resolve eq24548 eq143126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24548 eq143126
  have eq146166 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by grind
  clear eq146054
  have eq146430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq146166 eq143002
    | exact resolve eq143002 eq146166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143002 eq146166
  have eq146541 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq146430
  have eq146580 : x = y := by
    first
    | (have r₁ := eq146541
       have r₂ := eq28
       grind)
    | exact resolve eq146541 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146541
  have eq146589 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq146580
       grind)
    | exact superpose eq146580 eq19
    | exact resolve eq19 eq146580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq146590 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq146580
       grind)
    | exact superpose eq146580 eq25
    | exact resolve eq25 eq146580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq146580
  have eq146713 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq146590
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq146590
    | exact resolve eq146590 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq146590
  have eq146735 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq146713 eq27
    | exact resolve eq27 eq146713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq146713
  have eq147065 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq146735 eq86
    | exact resolve eq86 eq146735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq146735
  have eq147214 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq147065
       have i₂ := eq146589
       grind)
    | exact superpose eq146589 eq147065
    | exact resolve eq147065 eq146589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146589 eq147065
  have eq147240 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq147214 eq15
    | exact resolve eq15 eq147214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147214
  have eq147320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq147240
    | exact resolve eq147240 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq147240
  have eq147343 : False := by grind
  exact eq147343

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxx_pxy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X2 X2) X0
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq34 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq34 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq39
    | exact resolve eq39 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq39
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq97 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq20 X0 X0 X2 X1
       grind)
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq20 X0 X1 X2 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X1 X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op X2 X3) X1 X0 X4
       have i₂ := eq22 X2 X3 X1 X0
       grind)
    | exact superpose eq22 eq20
    | exact resolve eq20 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X0) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X2 X3) X1
       have i₂ := eq22 X2 X3 X1 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq230 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq10
    | exact resolve eq10 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq619 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq46 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq13 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq644 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq654 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq644 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq644
    | (have j0 := eq644 X0 X1
       grind)
    | exact resolve eq644 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq655 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq654 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq663 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq655 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq655
    | (have j0 := eq655 X0 X1
       grind)
    | exact resolve eq655 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq664 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq663 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq705 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X3 X4) (M.op X2 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq97 X3 X4 (M.op X2 X5) X0
       have i₂ := eq97 X2 X5 X0 X1
       grind)
    | (have i₁ := eq97 X3 X4 (M.op X2 X5) X0
       have i₂ := eq97 X0 X1 X2 X5
       grind)
    | exact superpose eq97 eq97
    | exact resolve eq97 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1300 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0 (σ (M.op X0 X0))
       have i₂ := eq40 (M.op X0 X0)
       grind)
    | exact superpose eq40 eq113
    | exact resolve eq113 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3989 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (σ (M.op X0 X0))) = (M.op (M.op (M.op X2 X3) X4) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq216 X1 (σ X0) X2 X3 X4
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq216
    | exact resolve eq216 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq4336 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (σ (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq217 X1 (σ X0) X2 X3
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq217
    | exact resolve eq217 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4437 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq217 X1 X2 (σ X0) (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq217
    | exact resolve eq217 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq217
  have eq9623 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq664 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq664
    | exact resolve eq664 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9635 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq664 x y
       grind)
    | exact superpose eq664 eq16
    | (have j1 := eq664 x x
       grind)
    | exact resolve eq16 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq9774 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9623 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9623
    | (have j0 := eq9623 X0 X1
       grind)
    | exact resolve eq9623 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq9623
  have eq9786 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9774 X0 X1
       have i₂ := eq230 X0
       grind)
    | exact superpose eq230 eq9774
    | (have j0 := eq9774 X0 X1
       grind)
    | exact resolve eq9774 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq9774
  have eq9792 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9786 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq9786
    | (have j0 := eq9786 X0 X1
       grind)
    | exact resolve eq9786 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9786
  have eq10504 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9792 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9792
    | (have j0 := eq9792 X1 X1
       grind)
    | exact resolve eq9792 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9792
  have eq11364 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq10504 (τ X1) X0
       grind)
    | exact superpose eq10504 eq17
    | (have j1 := eq10504 X0 X0
       grind)
    | exact resolve eq17 eq10504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq10504
  have eq16260 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) (M.op X5 X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq97 X0 X1 (M.op X2 X3) X5
       have i₂ := eq705 X2 X3 X5 X0 X4 X6
       grind)
    | (have i₁ := eq97 (M.op X2 X5) X1 X3 X4
       have i₂ := eq705 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq705 eq97
    | exact resolve eq97 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq107092 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (σ (M.op (M.op X0 X1) (M.op X2 X3))) X5) = (M.op (M.op X5 X5) (σ (M.op X0 X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq113 (M.op X0 X4) X5
       have i₂ := eq16260 X0 X4 X0 X4 X1 X2 X3
       grind)
    | (have i₁ := eq113 (M.op X0 X4) X5
       have i₂ := eq16260 X0 X1 X2 X3 X4 X0 X4
       grind)
    | exact superpose eq16260 eq113
    | exact resolve eq113 eq16260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190590 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11364 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11364
    | (have j0 := eq11364 X1 X1
       grind)
    | exact resolve eq11364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11364
  have eq190943 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190590 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq190590
    | (have j0 := eq190590 X0 X1
       grind)
    | exact resolve eq190590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190590
  have eq325327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9635
       have i₂ := eq190943 y x
       grind)
    | exact superpose eq190943 eq9635
    | (have j1 := eq190943 x x
       grind)
    | (have r₁ := eq9635
       have r₂ := eq190943 y x
       grind)
    | exact resolve eq9635 eq190943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9635 eq190943
  have eq325328 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq325327
  have eq343244 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq325328
       grind)
    | exact superpose eq325328 eq10
    | exact resolve eq10 eq325328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325328
  have eq343369 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq343244
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq343244
    | exact resolve eq343244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343244
  have eq343370 : x = (M.op x x) := by grind
  clear eq343369
  have eq356318 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq108 x X0 X1
       have i₂ := eq343370
       grind)
    | exact superpose eq343370 eq108
    | exact resolve eq108 eq343370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq356320 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq113 x X0
       have i₂ := eq343370
       grind)
    | exact superpose eq343370 eq113
    | exact resolve eq113 eq343370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq356446 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4336 x X0 X1 X2
       have i₂ := eq343370
       grind)
    | exact superpose eq343370 eq4336
    | exact resolve eq4336 eq343370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4336
  have eq356448 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq4437 x X0 X1
       have i₂ := eq343370
       grind)
    | exact superpose eq343370 eq4437
    | exact resolve eq4437 eq343370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4437
  have eq356521 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 x X0 X1 x
       have i₂ := eq343370
       grind)
    | exact superpose eq343370 eq20
    | exact resolve eq20 eq343370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq356530 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1 x x
       have i₂ := eq343370
       grind)
    | exact superpose eq343370 eq97
    | exact resolve eq97 eq343370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq356636 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (σ (M.op X1 X1))) = (M.op (M.op x X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3989 X1 X0 x x X2
       have i₂ := eq343370
       grind)
    | exact superpose eq343370 eq3989
    | exact resolve eq3989 eq343370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989
  have eq356647 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) x) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16260 X0 X1 X2 X3 X4 x x
       have i₂ := eq343370
       grind)
    | exact superpose eq343370 eq16260
    | exact resolve eq16260 eq343370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16260 eq343370
  have eq356728 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op x X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq356647 X0 X1 X2 X3 x
       have i₂ := eq356530 X0 x
       grind)
    | exact superpose eq356530 eq356647
    | exact resolve eq356647 eq356530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356530 eq356647
  have eq356752 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op X1 X1))) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq356636 X0 X1 x
       have i₂ := eq356521 x X0
       grind)
    | exact superpose eq356521 eq356636
    | exact resolve eq356636 eq356521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356521 eq356636
  have eq356887 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (σ x))) = (M.op (σ (M.op (M.op X0 X0) (σ x))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1300 x
       have i₂ := eq356448 x x
       grind)
    | exact superpose eq356448 eq1300
    | exact resolve eq1300 eq356448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq356448
  have eq371751 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (σ x) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq356446 X0 X1 X2
       have i₂ := eq356320 X0
       grind)
    | exact superpose eq356320 eq356446
    | exact resolve eq356446 eq356320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356320 eq356446
  have eq378377 : ∀ X0 X4 X5 : G, (M.op (M.op X5 X5) (σ (M.op X0 X4))) = (M.op (σ (M.op x X0)) X5) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq107092 X0 x x x X4 X5
       have i₂ := eq356728 X0 x x x
       grind)
    | exact superpose eq356728 eq107092
    | exact resolve eq107092 eq356728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107092
  have eq408661 : ∀ X0 : G, (σ (M.op (σ x) X0)) = (M.op (σ (M.op (σ x) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq356887 x
       have i₂ := eq356318 x x
       grind)
    | exact superpose eq356318 eq356887
    | exact resolve eq356887 eq356318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356318 eq356887
  have eq413281 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq371751 X0 x x
       have i₂ := eq356728 X0 X0 x x
       grind)
    | exact superpose eq356728 eq371751
    | exact resolve eq371751 eq356728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356728 eq371751
  have eq425213 : ∀ X0 X1 : G, (M.op x X0) = (M.op (σ (M.op x X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq356752 X0 X1
       have i₂ := eq378377 X1 X1 X0
       grind)
    | exact superpose eq378377 eq356752
    | exact resolve eq356752 eq378377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356752 eq378377
  have eq446848 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ (M.op x X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq408661 X0
       have i₂ := eq413281 X0
       grind)
    | exact superpose eq413281 eq408661
    | exact resolve eq408661 eq413281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408661
  have eq447542 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq413281 (σ y)
       grind)
    | exact superpose eq413281 eq16
    | exact resolve eq16 eq413281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413281
  have eq474250 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq446848 X0
       have i₂ := eq425213 (σ X0) X0
       grind)
    | exact superpose eq425213 eq446848
    | exact resolve eq446848 eq425213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425213 eq446848
  have eq498703 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq447542
       have i₂ := eq474250 y
       grind)
    | exact superpose eq474250 eq447542
    | (have r₁ := eq447542
       have r₂ := eq474250 y
       grind)
    | exact resolve eq447542 eq474250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447542 eq474250
  have eq498704 : False := by grind
  exact eq498704

/-- `Equation4646`: `(x ◇ y) ◇ x = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_pxx_pxx_pyx_Equation4646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op x y) y) := by
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
  have eq182 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X3 X1)
       have i₂ := eq16 X3 X1 X0
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X2 X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (M.op (M.op x y) x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 x
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X0 X1) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op y X1)
       have i₂ := eq16 y X1 X0
       grind)
    | (have i₁ := eq175 (M.op x y)
       have i₂ := eq16 X0 y x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (M.op (M.op X1 y) y) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) y X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq197 X0 x
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq197
    | exact resolve eq197 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq197
  have eq210 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq176 eq216
    | exact resolve eq216 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq239 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op x y) y) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) X0 X1
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq176 (M.op sF3 y)
       have i₂ := eq181 sF3
       grind)
    | exact superpose eq181 eq176
    | exact resolve eq176 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq242 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq188 eq241
    | exact resolve eq241 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq243 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op X0 y)) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq188 eq239
    | exact resolve eq239 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq251 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq198 eq243
    | exact resolve eq243 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq243
  have eq266 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : (M.op (M.op x y) y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op y (σ y))) := by
    first
    | exact superpose eq182 eq181
    | exact resolve eq181 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq182
  have eq272 : (M.op (M.op x y) y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op y (σ y))) := by
    first
    | exact superpose eq210 eq268
    | exact resolve eq268 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq274 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq210 eq266
    | exact resolve eq266 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq266
  have eq282 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq217 eq272
    | exact resolve eq272 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq272
  have eq287 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq188 eq282
    | exact resolve eq282 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq282
  have eq392 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have i₁ := eq251 X0 (M.op X0 y)
       have i₂ := eq195 X0
       grind)
    | (have i₁ := eq251 x (M.op x y)
       have i₂ := eq195 X0
       grind)
    | exact superpose eq195 eq251
    | exact resolve eq251 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq413 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq251 X1 x
       grind)
    | exact superpose eq251 eq16
    | exact resolve eq16 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq580 : (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq392 eq187
    | exact resolve eq187 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq599 : ∀ X0 : G, (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq392 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op x y) x)
       have r₂ := eq392 (M.op (M.op x y) x)
       grind)
    | exact resolve eq28 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq600 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have j0 := eq599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq657 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq666 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq674 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq674 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq814 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq600 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq600
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq871 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq928 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq956 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq871 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq871
    | exact resolve eq871 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq1008 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq600 eq928
    | exact resolve eq928 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7307 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq657
       grind)
    | exact superpose eq657 eq40
    | exact resolve eq40 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq7308 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7307
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7307
    | exact resolve eq7307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7307
  have eq7310 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq7308
    | exact resolve eq7308 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7308
  have eq21474 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq600 (M.op sF0 x)
       have i₂ := eq833 (M.op sF0 x)
       grind)
    | exact superpose eq833 eq600
    | (have j1 := eq833 X0
       grind)
    | exact resolve eq600 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq21583 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21474 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq21474 X0
       have r₂ := eq13 X0 (k X0 X0)
       grind)
    | (have r₁ := eq21474 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq21474 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq21474 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21474
  have eq21676 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq600 X0
       have i₂ := eq21583 X0
       grind)
    | exact superpose eq21583 eq600
    | exact resolve eq600 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21707 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq413 X0 X0
       have i₂ := eq21583 X0
       grind)
    | exact superpose eq21583 eq413
    | exact resolve eq413 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21722 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) x))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1008 X0
       have i₂ := eq21583 (σ X0)
       grind)
    | exact superpose eq21583 eq1008
    | exact resolve eq1008 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq21743 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) x))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq21722 X0
       have i₂ := eq928 X0 (σ X0)
       grind)
    | exact superpose eq928 eq21722
    | exact resolve eq21722 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21722
  have eq21781 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (M.op x y) x))) := by
    intro X0
    first
    | (have i₁ := eq21743 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq21743
    | exact resolve eq21743 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21743
  have eq22003 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq21676 (σ X0)
       grind)
    | exact superpose eq21676 eq10
    | exact resolve eq10 eq21676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21676
  have eq22134 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21707 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq21707
    | exact resolve eq21707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22135 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq21707 (τ X0)
       have i₂ := eq956 X0 X0
       grind)
    | exact superpose eq956 eq21707
    | exact resolve eq21707 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23742 : (σ (M.op (M.op x y) x)) = (k (σ (M.op (M.op x y) x)) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq580 eq22003
    | exact resolve eq22003 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22003
  have eq24422 : (M.op (M.op x y) x) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq580 eq22134
    | exact resolve eq22134 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24619 : (M.op (M.op x y) x) = (k (σ (M.op (M.op x y) x)) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq24422
       have i₂ := eq600 (σ (M.op sF0 x))
       grind)
    | exact superpose eq600 eq24422
    | exact resolve eq24422 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq24422
  have eq29090 : (τ (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) (τ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq24619 eq928
    | exact resolve eq928 eq24619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq29099 : (k (M.op (M.op x y) x) (M.op (M.op x y) x)) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq21781 eq29090
    | exact resolve eq29090 eq21781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21781 eq29090
  have eq29101 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq580 eq29099
    | exact resolve eq29099 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq29099
  have eq29117 : (M.op (M.op x y) x) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq29101 eq14
    | exact resolve eq14 eq29101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29101
  have eq37417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7310 eq666
    | exact resolve eq666 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq7310
  have eq37426 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq37417
       have r₂ := eq27
       grind)
    | exact resolve eq37417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37417
  have eq37433 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq37426
       have i₂ := eq21583 sF2
       grind)
    | exact superpose eq21583 eq37426
    | exact resolve eq37426 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37426
  have eq37438 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq37433
       have i₂ := eq21583 sF3
       grind)
    | exact superpose eq21583 eq37433
    | exact resolve eq37433 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37433
  have eq37443 : x = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq37438
       have i₂ := eq21583 x
       grind)
    | exact superpose eq21583 eq37438
    | exact resolve eq37438 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37438
  have eq37445 : (σ x) = (k (σ y) (σ y)) ∨ x = (k x x) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37443
       have i₂ := eq21583 y
       grind)
    | exact superpose eq21583 eq37443
    | exact resolve eq37443 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37443
  have eq37450 : (τ (σ x)) = (k y y) ∨ x = (k x x) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq37445 eq116
    | exact resolve eq116 eq37445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq37445
  have eq37478 : x = (k y y) ∨ x = (k x x) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq30 eq37450
    | exact resolve eq37450 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37450
  have eq37479 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ x = (k y y) := by grind
  clear eq37478
  have eq37496 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq37479 eq142
    | exact resolve eq142 eq37479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq37479
  have eq37527 : x = (k x x) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq37496
    | exact resolve eq37496 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37496
  have eq37528 : x = (k y y) ∨ x = (k x x) := by grind
  clear eq37527
  have eq37558 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq21707 y
       have i₂ := eq37528
       grind)
    | exact superpose eq37528 eq21707
    | exact resolve eq21707 eq37528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37559 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq22134 y
       have i₂ := eq37528
       grind)
    | exact superpose eq37528 eq22134
    | exact resolve eq22134 eq37528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37528
  have eq37567 : (M.op (M.op x y) x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq37559
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37559
    | exact resolve eq37559 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37559
  have eq37568 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq37558
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37558
    | exact resolve eq37558 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37558
  have eq37580 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq37567
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37567
    | exact resolve eq37567 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37567
  have eq37587 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (k x x) := by
    first
    | exact superpose eq26 eq37580
    | exact resolve eq37580 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37580
  have eq37590 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37568 eq37587
    | exact resolve eq37587 eq37568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37587
  have eq37599 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq37590
       grind)
    | exact superpose eq37590 eq40
    | exact resolve eq40 eq37590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37608 : (M.op (M.op x y) x) = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21707 x
       have i₂ := eq37590
       grind)
    | exact superpose eq37590 eq21707
    | exact resolve eq21707 eq37590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37609 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22134 x
       have i₂ := eq37590
       grind)
    | exact superpose eq37590 eq22134
    | exact resolve eq22134 eq37590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22134
  have eq37610 : (M.op (M.op x y) x) = (M.op (τ x) (τ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22135 x
       have i₂ := eq37590
       grind)
    | exact superpose eq37590 eq22135
    | exact resolve eq22135 eq37590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37622 : (M.op (M.op x y) x) = (k (τ x) (τ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37610
       have i₂ := eq21583 (τ x)
       grind)
    | exact superpose eq21583 eq37610
    | exact resolve eq37610 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37610
  have eq37623 : (M.op (M.op x y) x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37609
       have i₂ := eq21583 (σ x)
       grind)
    | exact superpose eq21583 eq37609
    | exact resolve eq37609 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37609
  have eq37624 : (k x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37608
       have i₂ := eq21583 x
       grind)
    | exact superpose eq21583 eq37608
    | exact resolve eq37608 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37608
  have eq37629 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37599
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37599
    | exact resolve eq37599 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37599
  have eq37636 : (M.op (M.op x y) x) = (τ (k x x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37622
       have i₂ := eq956 x x
       grind)
    | exact superpose eq956 eq37622
    | exact resolve eq37622 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37622
  have eq37637 : (σ (k x x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37623
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq37623
    | exact resolve eq37623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37623
  have eq37638 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37590 eq37624
    | exact resolve eq37624 eq37590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37624
  have eq37643 : (M.op (M.op x y) x) = (τ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37590 eq37636
    | exact resolve eq37636 eq37590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37590 eq37636
  have eq37644 : (k (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37637
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq37637
    | exact resolve eq37637 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37637
  have eq37648 : x = (τ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37638 eq37643
    | exact resolve eq37643 eq37638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37643
  have eq37649 : (k (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37644
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37644
    | exact resolve eq37644 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37644
  have eq37653 : (σ x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37629 eq37649
    | exact resolve eq37649 eq37629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37629 eq37649
  have eq37659 : x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x
       have i₂ := eq37648
       grind)
    | exact superpose eq37648 eq14
    | exact resolve eq14 eq37648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37648
  have eq37724 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq37659
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37659
    | exact resolve eq37659 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37659
  have eq37755 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq37724 eq27
    | exact resolve eq27 eq37724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38206 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37638 eq392
    | exact resolve eq392 eq37638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq38409 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37724 eq38206
    | exact resolve eq38206 eq37724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38206
  have eq38570 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37653 eq242
    | exact resolve eq242 eq37653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq37653
  have eq38766 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq287 eq38570
    | exact resolve eq38570 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq38570
  have eq38830 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq38766
    | exact resolve eq38766 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq38766
  have eq38870 : x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37638 eq38830
    | exact resolve eq38830 eq37638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37638 eq38830
  have eq38886 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37724 eq38870
    | exact resolve eq38870 eq37724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37724 eq38870
  have eq38913 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq38886
  have eq39579 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq37568 eq29117
    | exact resolve eq29117 eq37568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29117 eq37568
  have eq39624 : x = (k x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq39579
    | exact resolve eq39579 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39579
  have eq39804 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq39624
       grind)
    | exact superpose eq39624 eq40
    | exact resolve eq40 eq39624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq39813 : (M.op (M.op x y) x) = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq21707 x
       have i₂ := eq39624
       grind)
    | exact superpose eq39624 eq21707
    | exact resolve eq21707 eq39624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39815 : (M.op (M.op x y) x) = (M.op (τ x) (τ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq22135 x
       have i₂ := eq39624
       grind)
    | exact superpose eq39624 eq22135
    | exact resolve eq22135 eq39624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22135
  have eq39827 : (M.op (M.op x y) x) = (k (τ x) (τ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39815
       have i₂ := eq21583 (τ x)
       grind)
    | exact superpose eq21583 eq39815
    | exact resolve eq39815 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39815
  have eq39829 : (k x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39813
       have i₂ := eq21583 x
       grind)
    | exact superpose eq21583 eq39813
    | exact resolve eq39813 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39813
  have eq39834 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39804
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39804
    | exact resolve eq39804 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39804
  have eq39841 : (M.op (M.op x y) x) = (τ (k x x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39827
       have i₂ := eq956 x x
       grind)
    | exact superpose eq956 eq39827
    | exact resolve eq39827 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956 eq39827
  have eq39843 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39624 eq39829
    | exact resolve eq39829 eq39624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39829
  have eq39848 : (M.op (M.op x y) x) = (τ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39624 eq39841
    | exact resolve eq39841 eq39624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39624 eq39841
  have eq39853 : x = (τ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39843 eq39848
    | exact resolve eq39848 eq39843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39843 eq39848
  have eq39864 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq14 x
       have i₂ := eq39853
       grind)
    | exact superpose eq39853 eq14
    | exact resolve eq14 eq39853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39853
  have eq39929 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39864
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39864
    | exact resolve eq39864 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39864
  have eq39943 : x = (σ x) := by
    first
    | (have r₁ := eq39929
       have r₂ := eq37755
       grind)
    | exact resolve eq39929 eq37755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37755 eq39929
  have eq39966 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq39943
       grind)
    | exact superpose eq39943 eq18
    | exact resolve eq18 eq39943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq39967 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq39943
       grind)
    | exact superpose eq39943 eq22
    | exact resolve eq22 eq39943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq40215 : (σ x) = (τ (σ x)) := by
    first
    | exact superpose eq39967 eq15
    | exact resolve eq15 eq39967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39967
  have eq40565 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39966 eq38409
    | exact resolve eq38409 eq39966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38409
  have eq40604 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq40565
       have r₂ := eq38913
       grind)
    | exact resolve eq40565 eq38913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38913 eq40565
  have eq40619 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq40604 eq27
    | exact resolve eq27 eq40604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41721 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39834 eq675
    | (have j0 := eq675 (σ x)
       grind)
    | (have r₁ := eq675 (σ x)
       have r₂ := eq39834
       grind)
    | exact resolve eq675 eq39834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq41730 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39834 eq21707
    | exact resolve eq21707 eq39834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21707 eq39834
  have eq41740 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq41721
  have eq41746 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq41730
       have r₂ := eq40619
       grind)
    | exact resolve eq41730 eq40619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41730
  have eq41754 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq41740
       have r₂ := eq40619
       grind)
    | exact resolve eq41740 eq40619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41740
  have eq41765 : (k (σ x) (σ x)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq41746
       have i₂ := eq21583 sF2
       grind)
    | exact superpose eq21583 eq41746
    | exact resolve eq41746 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41746
  have eq41770 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq41754
       have i₂ := eq21583 sF2
       grind)
    | exact superpose eq21583 eq41754
    | exact resolve eq41754 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41754
  have eq41781 : (k (σ x) (σ x)) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq41765
       have i₂ := eq39943
       grind)
    | exact superpose eq39943 eq41765
    | exact resolve eq41765 eq39943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41765
  have eq41795 : (σ x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq41770 eq41781
    | exact resolve eq41781 eq41770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41781
  have eq41912 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ x) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq41795 eq183
    | exact resolve eq183 eq41795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41916 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ x)) y) := by
    first
    | exact superpose eq41795 eq189
    | exact resolve eq189 eq41795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq41920 : (M.op (M.op x y) x) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq41795 eq413
    | exact resolve eq413 eq41795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41923 : (M.op (M.op x y) (σ x)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq41920
       have i₂ := eq39943
       grind)
    | exact superpose eq39943 eq41920
    | exact resolve eq41920 eq39943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41920
  have eq41927 : (M.op (M.op x y) x) = (M.op (k (σ x) (σ x)) y) := by
    first
    | (have i₁ := eq41916
       have i₂ := eq21583 sF2
       grind)
    | exact superpose eq21583 eq41916
    | exact resolve eq41916 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41916
  have eq41931 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k (σ x) (σ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41912 X0 X1
       have i₂ := eq21583 sF2
       grind)
    | exact superpose eq21583 eq41912
    | exact resolve eq41912 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41912
  have eq41943 : (σ x) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq41795 eq41923
    | exact resolve eq41923 eq41795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41923
  have eq41947 : (M.op (M.op x y) x) = (M.op (σ x) y) := by
    first
    | exact superpose eq41770 eq41927
    | exact resolve eq41927 eq41770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41927
  have eq41951 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | exact superpose eq41770 eq41931
    | exact resolve eq41931 eq41770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41770 eq41931
  have eq41964 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq39966 eq41947
    | exact resolve eq41947 eq39966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39966 eq41947
  have eq41967 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq41951 x X1
       have i₂ := eq413 x X1
       grind)
    | (have i₁ := eq41951 x y
       have i₂ := eq413 x X1
       grind)
    | exact superpose eq413 eq41951
    | exact resolve eq41951 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41951
  have eq41978 : (M.op x y) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq41964
       have i₂ := eq39943
       grind)
    | exact superpose eq39943 eq41964
    | exact resolve eq41964 eq39943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41964
  have eq41979 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (M.op x y) (σ x)) := by
    intro X1
    first
    | (have i₁ := eq41967 X1
       have i₂ := eq39943
       grind)
    | exact superpose eq39943 eq41967
    | exact resolve eq41967 eq39943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41967
  have eq41988 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | exact superpose eq41795 eq41979
    | exact resolve eq41979 eq41795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41979
  have eq42000 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ x) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq41943 eq183
    | exact resolve eq183 eq41943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq42020 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | exact superpose eq41943 eq42000
    | exact resolve eq42000 eq41943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41943 eq42000
  have eq42038 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq41988 eq42020
    | exact resolve eq42020 eq41988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41988 eq42020
  have eq42064 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq41978 eq41795
    | exact resolve eq41795 eq41978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42082 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41978 eq413
    | exact resolve eq413 eq41978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq41978
  have eq42085 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq42082
       have i₂ := eq21583 sF0
       grind)
    | exact superpose eq21583 eq42082
    | exact resolve eq42082 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42082
  have eq42102 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq42085
       have i₂ := eq39943
       grind)
    | exact superpose eq39943 eq42085
    | exact resolve eq42085 eq39943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39943 eq42085
  have eq42117 : (σ x) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41795 eq42102
    | exact resolve eq42102 eq41795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41795 eq42102
  have eq42128 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq42064 eq42117
    | exact resolve eq42117 eq42064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42117
  have eq42143 : x = (τ (M.op x y)) := by
    first
    | exact superpose eq42064 eq30
    | exact resolve eq30 eq42064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq42181 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq42064 eq274
    | exact resolve eq274 eq42064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq42219 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq42064 eq40215
    | exact resolve eq40215 eq42064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40215
  have eq42248 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq40604 eq42181
    | exact resolve eq42181 eq40604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40604 eq42181
  have eq42286 : x = (M.op x y) := by
    first
    | exact superpose eq42219 eq42143
    | exact resolve eq42143 eq42219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42143 eq42219
  have eq42308 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42248 X0 X1
       have i₂ := eq21583 sF0
       grind)
    | exact superpose eq21583 eq42248
    | exact resolve eq42248 eq21583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21583 eq42248
  have eq42359 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq42128 eq42308
    | exact resolve eq42308 eq42128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42128 eq42308
  have eq42398 : ∀ X1 : G, (σ x) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have i₁ := eq42359 x X1
       have i₂ := eq42038 x X1
       grind)
    | exact superpose eq42038 eq42359
    | exact resolve eq42359 eq42038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42038 eq42359
  have eq42420 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | exact superpose eq42064 eq42398
    | exact resolve eq42398 eq42064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42064 eq42398
  have eq42521 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq23742
       have i₂ := eq42286
       grind)
    | exact superpose eq42286 eq23742
    | exact resolve eq23742 eq42286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23742
  have eq42525 : (M.op (M.op x y) (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq24619
       have i₂ := eq42286
       grind)
    | exact superpose eq42286 eq24619
    | exact resolve eq24619 eq42286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24619 eq42286
  have eq42581 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq42420 eq42525
    | exact resolve eq42525 eq42420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42525
  have eq42585 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq42420 eq42521
    | exact resolve eq42521 eq42420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42420 eq42521
  have eq42689 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq20 eq42581
    | exact resolve eq42581 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42581
  have eq42691 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq20 eq42585
    | exact resolve eq42585 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq42585
  have eq42753 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq42689 eq42691
    | exact resolve eq42691 eq42689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42689 eq42691
  have eq42783 : False := by grind
  exact eq42783

/-- `Equation4661`: `(x ◇ y) ◇ y = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pyx_Equation4661 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4661 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4661.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X1 X2) X2) := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X1 X2) X2 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | (have i₁ := eq16 (M.op X0 X1) X1 X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X1 X2 X3
       grind)
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (σ (M.op y y)) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq36
    | exact resolve eq36 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq179 X1
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq204 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X1) X1) := by
    intro X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq207 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq204 x
       have i₂ := eq193 sF2 x
       grind)
    | exact superpose eq193 eq204
    | (have j1 := eq193 (σ x) (σ y)
       grind)
    | exact resolve eq204 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq221 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq193 (M.op x X1) X1
       have i₂ := eq193 x X1
       grind)
    | (have i₁ := eq193 (M.op x y) y
       have i₂ := eq193 x X1
       grind)
    | exact superpose eq193 eq193
    | exact resolve eq193 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
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
  have eq287 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
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
  have eq374 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq221 eq174
    | exact resolve eq174 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq891 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq901 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq906 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq907 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq906 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq960 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq907 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq907
    | (have j0 := eq907 (σ X0)
       grind)
    | exact resolve eq907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2296 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq891
       grind)
    | exact superpose eq891 eq39
    | exact resolve eq39 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq2297 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2296
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2296
    | exact resolve eq2296 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2296
  have eq2299 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2297
    | exact resolve eq2297 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq16789 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq374 eq960
    | (have j0 := eq960 (M.op (M.op x y) y)
       grind)
    | exact resolve eq960 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq16825 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq16789
  have eq16953 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq16825 eq184
    | exact resolve eq184 eq16825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq16954 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq16825 eq193
    | exact resolve eq193 eq16825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16957 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (σ (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq16825 eq16953
    | exact resolve eq16953 eq16825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16953
  have eq16969 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq16957 x x
       have i₂ := eq193 x x
       grind)
    | (have i₁ := eq16957 x y
       have i₂ := eq193 x x
       grind)
    | exact superpose eq193 eq16957
    | (have j0 := eq16957 x y
       grind)
    | exact resolve eq16957 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16957
  have eq16984 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq16969 eq15
    | exact resolve eq15 eq16969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2299 eq901
    | exact resolve eq901 eq2299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18054 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18047
       have r₂ := eq27
       grind)
    | exact resolve eq18047 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18047
  have eq18061 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18054 eq287
    | exact resolve eq287 eq18054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq18054
  have eq18085 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq18061
    | exact resolve eq18061 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18061
  have eq18094 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq18085
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq18085
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq18085
       have r₂ := eq13 y x
       grind)
    | exact resolve eq18085 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18085
  have eq18097 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18094 eq276
    | exact resolve eq276 eq18094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq18094
  have eq18121 : x = (k x x) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq18097
    | exact resolve eq18097 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18097
  have eq18130 : x = (k y x) ∨ x = (k x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq18121
       have r₂ := eq13 x x
       grind)
    | exact resolve eq18121 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18121
  have eq18133 : x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18130
       have i₂ := eq891
       grind)
    | exact superpose eq891 eq18130
    | exact resolve eq18130 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18136 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq891
       have i₂ := eq18130
       grind)
    | exact superpose eq18130 eq891
    | exact resolve eq891 eq18130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq18137 : (σ x) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq18130
       grind)
    | exact superpose eq18130 eq36
    | exact resolve eq36 eq18130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq18130
  have eq18140 : (σ x) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq18137
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18137
    | exact resolve eq18137 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18137
  have eq18141 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq907 x
       grind)
    | (have r₁ := eq18136
       have r₂ := eq907 x
       grind)
    | exact resolve eq18136 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18136
  have eq18144 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq18133
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq18133
       have r₂ := eq13 y x
       grind)
    | exact resolve eq18133 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18133
  have eq18148 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | exact superpose eq18140 eq2299
    | exact resolve eq2299 eq18140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299 eq18140
  have eq18160 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq907 x
       grind)
    | (have r₁ := eq18148
       have r₂ := eq907 x
       grind)
    | exact resolve eq18148 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq18148
  have eq18177 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq193 y y
       have i₂ := eq18141
       grind)
    | exact superpose eq18141 eq193
    | exact resolve eq193 eq18141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18141
  have eq18180 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18177
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18177
    | exact resolve eq18177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18177
  have eq18201 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq960 x
       have i₂ := eq18144
       grind)
    | exact superpose eq18144 eq960
    | (have j0 := eq960 x
       grind)
    | exact resolve eq960 eq18144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq18144
  have eq18208 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq18201
  have eq18209 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18208
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18208
    | exact resolve eq18208 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18208
  have eq18228 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq193 y y
       have i₂ := eq18160
       grind)
    | exact superpose eq18160 eq193
    | exact resolve eq193 eq18160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18160
  have eq18231 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18228
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18228
    | exact resolve eq18228 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18228
  have eq18538 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18180 eq16969
    | exact resolve eq16969 eq18180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18180
  have eq18560 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq18538
    | exact resolve eq18538 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18538
  have eq18581 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq175 x x X0 X1
       have i₂ := eq18560
       grind)
    | exact superpose eq18560 eq175
    | exact resolve eq175 eq18560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18587 : (M.op (M.op x y) y) = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq193 x x
       have i₂ := eq18560
       grind)
    | exact superpose eq18560 eq193
    | exact resolve eq193 eq18560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18590 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18560 eq18587
    | exact resolve eq18587 eq18560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18587
  have eq18594 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18581 X0 x
       have i₂ := eq193 X0 x
       grind)
    | (have i₁ := eq18581 x y
       have i₂ := eq193 X0 x
       grind)
    | exact superpose eq193 eq18581
    | exact resolve eq18581 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18581
  have eq18604 : ∀ X0 : G, x = (M.op (M.op x x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18590 eq18594
    | exact resolve eq18594 eq18590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18594
  have eq18608 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18560 eq18604
    | exact resolve eq18604 eq18560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18560 eq18604
  have eq18644 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18590 eq16969
    | exact resolve eq16969 eq18590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18590
  have eq18671 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18644
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18644
    | exact resolve eq18644 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18644
  have eq18686 : (M.op x y) = (τ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18671 eq28
    | exact resolve eq28 eq18671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq18969 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18608 y
       grind)
    | exact superpose eq18608 eq18
    | (have j1 := eq18608 y
       grind)
    | exact resolve eq18 eq18608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18608
  have eq18994 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq18969
  have eq19809 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ x)) X0) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq18209 eq175
    | exact resolve eq175 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19815 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18209 eq193
    | exact resolve eq193 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19818 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18209 eq19815
    | exact resolve eq19815 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19815
  have eq19822 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ x)) X0) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq19809 X0 x
       have i₂ := eq193 X0 x
       grind)
    | (have i₁ := eq19809 x y
       have i₂ := eq193 X0 x
       grind)
    | exact superpose eq193 eq19809
    | exact resolve eq19809 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19809
  have eq19831 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq18209 eq19822
    | exact resolve eq19822 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18209 eq19822
  have eq19835 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19818 eq19831
    | exact resolve eq19831 eq19818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19831
  have eq19883 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18231 eq16969
    | exact resolve eq16969 eq18231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18231
  have eq19912 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq19883
    | exact resolve eq19883 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19883
  have eq19918 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18994 eq19912
    | exact resolve eq19912 eq18994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19912
  have eq19939 : (M.op (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19918 eq193
    | exact resolve eq193 eq19918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19946 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19918 eq19939
    | exact resolve eq19939 eq19918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19918 eq19939
  have eq20294 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19946 eq16969
    | exact resolve eq16969 eq19946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16969 eq19946
  have eq20322 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq20294
    | exact resolve eq20294 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20294
  have eq20323 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq20322
  have eq20380 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq20323
  have eq21356 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19818 eq16984
    | exact resolve eq16984 eq19818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16984 eq19818
  have eq21397 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq21356
    | exact resolve eq21356 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21356
  have eq21419 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq175 y y X0 X1
       have i₂ := eq21397
       grind)
    | exact superpose eq21397 eq175
    | exact resolve eq175 eq21397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq21425 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq193 y y
       have i₂ := eq21397
       grind)
    | exact superpose eq21397 eq193
    | exact resolve eq193 eq21397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21397
  have eq21428 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq21425
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21425
    | exact resolve eq21425 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21425
  have eq21432 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq21419 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21419
    | (have j0 := eq21419 X0 X1
       grind)
    | exact resolve eq21419 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21419
  have eq21439 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq21432 X0 x
       have i₂ := eq193 X0 x
       grind)
    | (have i₁ := eq21432 x y
       have i₂ := eq193 X0 x
       grind)
    | exact superpose eq193 eq21432
    | exact resolve eq21432 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21432
  have eq21442 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq21428 eq21439
    | exact resolve eq21439 eq21428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21428 eq21439
  have eq22417 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19835 eq26
    | (have j1 := eq19835 (σ y)
       grind)
    | exact resolve eq26 eq19835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22483 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq186
       have i₂ := eq22417
       grind)
    | exact superpose eq22417 eq186
    | exact resolve eq186 eq22417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq22496 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq193 y y
       have i₂ := eq22417
       grind)
    | exact superpose eq22417 eq193
    | exact resolve eq193 eq22417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22417
  have eq22499 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22496
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22496
    | exact resolve eq22496 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22496
  have eq22506 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22483
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22483
    | exact resolve eq22483 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22483
  have eq22588 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22506 eq901
    | exact resolve eq901 eq22506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq22506
  have eq22592 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22588
  have eq30416 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22592 eq193
    | exact resolve eq193 eq22592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22592
  have eq30419 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq30416
    | exact resolve eq30416 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30416
  have eq30429 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22499 eq30419
    | exact resolve eq30419 eq22499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30419
  have eq30528 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30429 eq193
    | exact resolve eq193 eq30429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30531 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30429 eq30528
    | exact resolve eq30528 eq30429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30429 eq30528
  have eq30541 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22499 eq30531
    | exact resolve eq30531 eq22499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22499 eq30531
  have eq30559 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30541 eq207
    | exact resolve eq207 eq30541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq30563 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq30559
    | exact resolve eq30559 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30559
  have eq30566 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30541 eq30563
    | exact resolve eq30563 eq30541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30541 eq30563
  have eq30699 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30566 eq21442
    | exact resolve eq21442 eq30566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21442
  have eq30719 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by grind
  clear eq30699
  have eq30809 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq30719 eq27
    | exact resolve eq27 eq30719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30719
  have eq30811 : (M.op x y) = (σ x) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30809
       have r₂ := eq18671
       grind)
    | exact resolve eq30809 eq18671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18671 eq30809
  have eq30816 : x = (τ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30811 eq29
    | exact resolve eq29 eq30811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq30811
  have eq30987 : x = (M.op x y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18686 eq30816
    | exact resolve eq30816 eq18686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18686 eq30816
  have eq30988 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq30987
  have eq31032 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq30988
       grind)
    | exact superpose eq30988 eq18
    | exact resolve eq18 eq30988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31086 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  have eq31329 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31032 eq19835
    | exact resolve eq19835 eq31032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19835
  have eq31338 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq31329
  have eq31345 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq31338
       have r₂ := eq31086
       grind)
    | exact resolve eq31338 eq31086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31338
  have eq31352 : (σ x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30988 eq31345
    | exact resolve eq31345 eq30988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30988 eq31345
  have eq31390 : (M.op (M.op x y) y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq193 y y
       have i₂ := eq31352
       grind)
    | exact superpose eq31352 eq193
    | exact resolve eq193 eq31352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq31352
  have eq31403 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31032 eq31390
    | exact resolve eq31390 eq31032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31032 eq31390
  have eq31453 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31403 eq30566
    | exact resolve eq30566 eq31403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30566 eq31403
  have eq31465 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31453
  have eq31478 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31465
       have r₂ := eq31086
       grind)
    | exact resolve eq31465 eq31086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31086 eq31465
  have eq31507 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31478 eq27
    | exact resolve eq27 eq31478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31478
  have eq31515 : x = (M.op x y) := by
    first
    | (have r₁ := eq31507
       have r₂ := eq18994
       grind)
    | exact resolve eq31507 eq18994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18994 eq31507
  have eq31518 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31515
       grind)
    | exact superpose eq31515 eq18
    | exact resolve eq18 eq31515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31519 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq31515
       grind)
    | exact superpose eq31515 eq22
    | exact resolve eq22 eq31515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31515
  have eq31567 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31519 eq20
    | exact resolve eq20 eq31519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31519
  have eq32008 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq31518 eq221
    | exact resolve eq221 eq31518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq32012 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq31518 eq16825
    | exact resolve eq16825 eq31518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16825
  have eq32014 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq31518 eq16954
    | exact resolve eq16954 eq31518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16954 eq31518
  have eq32047 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq32014
    | exact resolve eq32014 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32014
  have eq32049 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq32012
    | exact resolve eq32012 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq32012
  have eq32055 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31567 eq32047
    | exact resolve eq32047 eq31567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32047
  have eq32057 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31567 eq32049
    | exact resolve eq32049 eq31567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31567 eq32049
  have eq32060 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq32055 eq32057
    | exact resolve eq32057 eq32055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32055 eq32057
  have eq32064 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq32060 eq26
    | exact resolve eq26 eq32060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq32144 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32060 eq20380
    | (have r₁ := eq20380
       have r₂ := eq32060
       grind)
    | exact resolve eq20380 eq32060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20380 eq32060
  have eq32168 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq32144
  have eq32226 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32008 eq32064
    | exact resolve eq32064 eq32008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32008 eq32064
  have eq32435 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq32226 eq27
    | exact resolve eq27 eq32226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32226
  have eq32443 : False := by grind
  exact eq32443

/-- `Equation4670`: `(x ◇ y) ◇ y = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_pxx_pxx_pyx_Equation4670 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4670 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4670.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X3) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  clear eq36
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
  have eq181 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
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
  have eq187 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq181 (M.op x X1) X1
       have i₂ := eq181 x X1
       grind)
    | (have i₁ := eq181 (M.op x y) y
       have i₂ := eq181 x X1
       grind)
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq189 eq187
    | exact resolve eq187 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq383 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq440 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq467 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq383 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq383
    | exact resolve eq383 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq648 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq189 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op x y) y)
       have r₂ := eq189 (M.op (M.op x y) y)
       grind)
    | exact resolve eq28 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq649 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have j0 := eq648 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq652 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | (have i₁ := eq181 X0 X0
       have i₂ := eq649 X0
       grind)
    | exact superpose eq649 eq181
    | exact resolve eq181 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 : G, (k X0 (M.op (M.op x y) y)) ≠ X1 ∨ (k X0 X1) = (k X0 (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq649 X0
       grind)
    | exact superpose eq649 eq13
    | (have r₁ := eq13 X0 (k X0 (M.op (M.op x y) y))
       have r₂ := eq649 X0
       grind)
    | exact resolve eq13 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq649 X0
       grind)
    | exact superpose eq649 eq11
    | exact resolve eq11 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq733 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq751 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq698 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq772 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq751 X0
       have j1 := eq657 X0 X0
       grind)
    | (have r₁ := eq751 X0
       have r₂ := eq657 X0 (k X0 X0)
       grind)
    | (have r₁ := eq751 (M.op (M.op x y) y)
       have r₂ := eq657 (M.op (M.op x y) y) (k (M.op (M.op x y) y) (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq751 x
       have r₂ := eq657 x x
       grind)
    | exact resolve eq751 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq751
  have eq798 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq652 (M.op sF0 y)
       have i₂ := eq772 (M.op sF0 y)
       grind)
    | exact superpose eq772 eq652
    | exact resolve eq652 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq799 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq649 (M.op sF0 y)
       have i₂ := eq772 (M.op sF0 y)
       grind)
    | exact superpose eq772 eq649
    | exact resolve eq649 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 : G, (τ (k (σ X0) (M.op (M.op x y) y))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq440 X0 (σ X0)
       have i₂ := eq772 (σ X0)
       grind)
    | (have i₁ := eq440 X0 (M.op (M.op x y) y)
       have i₂ := eq772 (σ X0)
       grind)
    | exact superpose eq772 eq440
    | exact resolve eq440 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq816 : ∀ X0 : G, (τ (k (σ X0) (M.op (M.op x y) y))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq812 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq812
    | exact resolve eq812 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq829 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq816 X0
       have i₂ := eq440 X0 (M.op sF0 y)
       grind)
    | exact superpose eq440 eq816
    | exact resolve eq816 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq887 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq798 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq798
    | exact resolve eq798 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq798 (τ X0)
       have i₂ := eq467 X0 X0
       grind)
    | exact superpose eq467 eq798
    | exact resolve eq798 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq250 eq887
    | exact resolve eq887 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1346 : (M.op (M.op x y) y) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq1288
       have i₂ := eq649 (σ (M.op sF0 y))
       grind)
    | exact superpose eq649 eq1288
    | exact resolve eq1288 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq1288
  have eq2722 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq722
       grind)
    | exact superpose eq722 eq40
    | exact resolve eq40 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq2723 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2722
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2722
    | exact resolve eq2722 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722
  have eq2725 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2723
    | exact resolve eq2723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723
  have eq2727 : x = (k x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2725
       have i₂ := eq799 x
       grind)
    | exact superpose eq799 eq2725
    | exact resolve eq2725 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2729 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq2727
       have i₂ := eq799 y
       grind)
    | exact superpose eq799 eq2727
    | exact resolve eq2727 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727
  have eq2732 : (τ (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq1346 eq440
    | exact resolve eq440 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq1346
  have eq2738 : (k (M.op (M.op x y) y) (M.op (M.op x y) y)) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq829 eq2732
    | exact resolve eq2732 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq2732
  have eq2741 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq250 eq2738
    | exact resolve eq2738 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq2738
  have eq2755 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq2741 eq14
    | exact resolve eq14 eq2741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741
  have eq30533 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq2729 eq733
    | exact resolve eq733 eq2729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq2729
  have eq30540 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | (have r₁ := eq30533
       have r₂ := eq27
       grind)
    | exact resolve eq30533 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30533
  have eq30546 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq30540
       have i₂ := eq799 sF2
       grind)
    | exact superpose eq799 eq30540
    | exact resolve eq30540 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30540
  have eq30548 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq30546
       have i₂ := eq799 sF3
       grind)
    | exact superpose eq799 eq30546
    | exact resolve eq30546 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30546
  have eq30554 : (τ (σ x)) = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq30548 eq116
    | exact resolve eq116 eq30548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq30548
  have eq30579 : x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq30554
    | exact resolve eq30554 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30554
  have eq30580 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by grind
  clear eq30579
  have eq30597 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq30580 eq142
    | exact resolve eq142 eq30580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq30580
  have eq30627 : x = (k x x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq30 eq30597
    | exact resolve eq30597 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq30597
  have eq30628 : x = (k y y) ∨ x = (k x x) := by grind
  clear eq30627
  have eq30654 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq798 y
       have i₂ := eq30628
       grind)
    | exact superpose eq30628 eq798
    | exact resolve eq798 eq30628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq30657 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq887 y
       have i₂ := eq30628
       grind)
    | exact superpose eq30628 eq887
    | exact resolve eq887 eq30628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30628
  have eq30665 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq30657
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30657
    | exact resolve eq30657 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq30657
  have eq30666 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq30654
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30654
    | exact resolve eq30654 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30654
  have eq30676 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq30665
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30665
    | exact resolve eq30665 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30665
  have eq30683 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | exact superpose eq26 eq30676
    | exact resolve eq30676 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30676
  have eq30685 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30666 eq30683
    | exact resolve eq30683 eq30666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30683
  have eq30694 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq30685
       grind)
    | exact superpose eq30685 eq40
    | exact resolve eq40 eq30685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30703 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq887 x
       have i₂ := eq30685
       grind)
    | exact superpose eq30685 eq887
    | exact resolve eq887 eq30685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30718 : (M.op (M.op x y) y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30703
       have i₂ := eq799 (σ x)
       grind)
    | exact superpose eq799 eq30703
    | exact resolve eq30703 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30703
  have eq30723 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30694
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30694
    | exact resolve eq30694 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30694
  have eq30730 : (σ (k x x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30718
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq30718
    | exact resolve eq30718 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30718
  have eq30736 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30730
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq30730
    | exact resolve eq30730 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30730
  have eq30741 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30736
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30736
    | exact resolve eq30736 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30736
  have eq30746 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30723 eq30741
    | exact resolve eq30741 eq30723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30741
  have eq30768 : (M.op (M.op x y) y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30723 eq888
    | exact resolve eq888 eq30723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30723
  have eq30781 : (M.op (M.op x y) y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30768
       have i₂ := eq799 (τ sF2)
       grind)
    | exact superpose eq799 eq30768
    | exact resolve eq30768 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30768
  have eq30795 : (τ (k (σ x) (σ x))) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30781
       have i₂ := eq467 sF2 sF2
       grind)
    | exact superpose eq467 eq30781
    | exact resolve eq30781 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30781
  have eq30802 : (k x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98 eq30795
    | exact resolve eq30795 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30795
  have eq30806 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30685 eq30802
    | exact resolve eq30802 eq30685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30685 eq30802
  have eq30810 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq30746 eq30806
    | exact resolve eq30806 eq30746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30806
  have eq30816 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq30810 eq27
    | exact resolve eq27 eq30810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30810
  have eq31869 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30746 eq189
    | exact resolve eq189 eq30746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq30746
  have eq32089 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31869 eq26
    | (have j1 := eq31869 (σ y)
       grind)
    | exact resolve eq26 eq31869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq32137 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq32089
  have eq32245 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq30666 eq2755
    | exact resolve eq2755 eq30666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755 eq30666
  have eq32266 : x = (k x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq32245
    | exact resolve eq32245 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32245
  have eq32394 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq32266
       grind)
    | exact superpose eq32266 eq40
    | exact resolve eq40 eq32266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32403 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq887 x
       have i₂ := eq32266
       grind)
    | exact superpose eq32266 eq887
    | exact resolve eq887 eq32266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq32421 : (M.op (M.op x y) y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32403
       have i₂ := eq799 (σ x)
       grind)
    | exact superpose eq799 eq32403
    | exact resolve eq32403 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32403
  have eq32426 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32394
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32394
    | exact resolve eq32394 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32394
  have eq32434 : (σ (k x x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32421
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq32421
    | exact resolve eq32421 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32421
  have eq32440 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32434
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq32434
    | exact resolve eq32434 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq32434
  have eq32445 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32440
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32440
    | exact resolve eq32440 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32440
  have eq32450 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32426 eq32445
    | exact resolve eq32445 eq32426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32445
  have eq32472 : (M.op (M.op x y) y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32426 eq888
    | exact resolve eq888 eq32426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq32426
  have eq32488 : (M.op (M.op x y) y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32472
       have i₂ := eq799 (τ sF2)
       grind)
    | exact superpose eq799 eq32472
    | exact resolve eq32472 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq32472
  have eq32503 : (τ (k (σ x) (σ x))) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32488
       have i₂ := eq467 sF2 sF2
       grind)
    | exact superpose eq467 eq32488
    | exact resolve eq32488 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq32488
  have eq32510 : (k x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq98 eq32503
    | exact resolve eq32503 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq32503
  have eq32514 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32266 eq32510
    | exact resolve eq32510 eq32266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32266 eq32510
  have eq32518 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32450 eq32514
    | exact resolve eq32514 eq32450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32514
  have eq32521 : x = (σ x) := by
    first
    | (have r₁ := eq32518
       have r₂ := eq30816
       grind)
    | exact resolve eq32518 eq30816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30816 eq32518
  have eq32522 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq32521
       grind)
    | exact superpose eq32521 eq18
    | exact resolve eq18 eq32521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq32523 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq32521
       grind)
    | exact superpose eq32521 eq22
    | exact resolve eq22 eq32521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq32521
  have eq32908 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32522 eq31869
    | exact resolve eq31869 eq32522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31869
  have eq32916 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32908
       have r₂ := eq32137
       grind)
    | exact resolve eq32908 eq32137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32137 eq32908
  have eq32925 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq32916 eq27
    | exact resolve eq27 eq32916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32916
  have eq33664 : (σ x) = (M.op (σ x) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32450 eq181
    | exact resolve eq181 eq32450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq32450
  have eq33669 : (σ x) = (M.op (σ x) y) := by
    first
    | (have r₁ := eq33664
       have r₂ := eq32925
       grind)
    | exact resolve eq33664 eq32925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33664
  have eq33740 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq32522 eq33669
    | exact resolve eq33669 eq32522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32522 eq33669
  have eq33974 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq33740 eq32523
    | exact resolve eq32523 eq33740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32523 eq33740
  have eq34351 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq33974 eq20
    | exact resolve eq20 eq33974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq33974
  have eq34507 : False := by grind
  exact eq34507

/-- `Equation575`: `x = y ◇ (z ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_x_pxy_Equation575 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law575 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law575.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
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
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq178 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq540 : ∀ X0 X1 X2 : G, (k X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 ∨ (M.op X2 (M.op X2 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 (M.op X2 (M.op X2 (M.op X1 X0)))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq28
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 (k X0 X1)))) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (M.op X1 (k X0 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq28 X0 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 (M.op X0 (M.op X1 X2))
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq541
       grind)
    | exact superpose eq541 eq41
    | exact resolve eq41 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq566
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq566
    | exact resolve eq566 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq569 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq567
    | exact resolve eq567 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq569 eq543
    | exact resolve eq543 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq577
       have r₂ := eq27
       grind)
    | exact resolve eq577 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq588 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq584 eq176
    | exact resolve eq176 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq584 eq27
    | exact resolve eq27 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : (σ y) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq588 (M.op sF3 sF3)
       have i₂ := eq178 sF3
       grind)
    | exact superpose eq178 eq588
    | exact resolve eq588 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) = (M.op X1 (M.op X1 (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq588 eq16
    | exact resolve eq16 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X1 : G, (σ y) = (M.op X1 (M.op X1 (σ y))) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq588 eq598
    | exact resolve eq598 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq598
  have eq606 : (σ y) = (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq599 (M.op sF3 sF3)
       have i₂ := eq178 sF3
       grind)
    | exact superpose eq178 eq599
    | exact resolve eq599 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq697 : (σ y) ≠ (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y))) ∨ (σ x) = (M.op (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y))) (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y)))) ∨ (σ x) = (k (σ x) (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq591 eq12
    | (have j0 := eq12 (σ x) (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y)))
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq591
       grind)
    | exact resolve eq12 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq698 : (σ x) = (M.op (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y))) (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y)))) ∨ (σ x) = (k (σ x) (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq697
       have r₂ := eq606
       grind)
    | exact resolve eq697 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq701 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq606 eq698
    | exact resolve eq698 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq703 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq606 eq701
    | exact resolve eq701 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq701
  have eq705 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq569 eq703
    | exact resolve eq703 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq720 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq705 eq178
    | exact resolve eq178 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq729 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq720
    | exact resolve eq720 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq569 eq729
    | exact resolve eq729 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq729
  have eq735 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq733
       have r₂ := eq27
       grind)
    | exact resolve eq733 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq737 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq735 eq29
    | exact resolve eq29 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq744 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq735 eq133
    | exact resolve eq133 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq747 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq735 eq589
    | exact resolve eq589 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq748 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq747
  have eq751 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq99 eq744
    | exact resolve eq744 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq744
  have eq758 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq737
    | exact resolve eq737 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq759 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq541 eq751
    | exact resolve eq751 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq751
  have eq762 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq758
       grind)
    | exact superpose eq758 eq18
    | exact resolve eq18 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq758
       grind)
    | exact superpose eq758 eq24
    | exact resolve eq24 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq763
    | exact resolve eq763 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq795 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq759 eq41
    | exact resolve eq41 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq795
    | exact resolve eq795 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq801 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq735 eq798
    | exact resolve eq798 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq798
  have eq807 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq762 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq762
       grind)
    | exact resolve eq12 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq807
  have eq1092 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq809 eq42
    | exact resolve eq42 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq809
  have eq1094 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1092
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1092
    | exact resolve eq1092 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1096 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq768 eq1094
    | exact resolve eq1094 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1102 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1096 eq543
    | exact resolve eq543 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1127 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1102 eq178
    | exact resolve eq178 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1134 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq762 eq1127
    | exact resolve eq1127 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq1127
  have eq1149 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1134 eq36
    | exact resolve eq36 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1156 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1149
    | exact resolve eq1149 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1158 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq768 eq1156
    | exact resolve eq1156 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1181 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1158 eq543
    | exact resolve eq543 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1190 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1181
  have eq1201 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1190 eq27
    | exact resolve eq27 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1203 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1201
       have r₂ := eq768
       grind)
    | exact resolve eq1201 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1214 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1203 eq176
    | exact resolve eq176 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1203 eq27
    | exact resolve eq27 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq768 eq1215
    | exact resolve eq1215 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq1215
  have eq1220 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq1217
  have eq1225 : ∀ X0 : G, (σ y) = (k (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op x y) ∨ (M.op X0 (M.op X0 (σ x))) = (M.op (σ x) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq1214 X0
       have i₂ := eq28 sF2 (M.op X0 (M.op X0 sF2))
       grind)
    | exact superpose eq28 eq1214
    | (have j1 := eq28 (σ x) (M.op X0 (M.op X0 (σ x)))
       grind)
    | exact resolve eq1214 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1229 : ∀ X0 : G, (σ y) = (k (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ (σ y) = (M.op X0 (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1214 eq28
    | exact resolve eq28 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1233 : ∀ X0 : G, (σ y) = (k (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1229 eq1225
    | (have j0 := eq1225 X0
       have j1 := eq1229 X0
       grind)
    | exact resolve eq1225 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq1229
  have eq1235 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1233
    | (have j0 := eq1233 X0
       grind)
    | exact resolve eq1233 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1236 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (k (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1203 eq1235
    | (have j0 := eq1235 X0
       grind)
    | exact resolve eq1235 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq1235
  have eq1237 : ∀ X0 : G, (σ y) = (k (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1236 X0
       grind)
    | (have r₁ := eq1236 X0
       have r₂ := eq1220
       grind)
    | exact resolve eq1236 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1242 : ∀ X0 : G, (τ (σ y)) = (k x (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1237 eq91
    | exact resolve eq91 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1237
  have eq1245 : ∀ X0 : G, y = (k x (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32 eq1242
    | exact resolve eq1242 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1247 : ∀ X0 : G, (M.op x y) = (k x (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq758 eq1245
    | exact resolve eq1245 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq1258 : ∀ X0 : G, (M.op x y) ≠ (τ (M.op X0 (M.op X0 (σ x)))) ∨ (τ (M.op X0 (M.op X0 (σ x)))) = (M.op x (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1247 eq559
    | (have j0 := eq559 x (τ (M.op X0 (M.op X0 (σ x))))
       grind)
    | exact resolve eq559 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1774 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op X2 (M.op X2 (M.op X1 (M.op X1 (M.op x y)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1779 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op X2 (M.op X2 (M.op X1 (M.op X1 (M.op (σ x) (σ y))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq176 eq177
    | exact resolve eq177 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1934 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) = X2 := by
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
  have eq2010 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1779 X0 x X0
       have i₂ := eq1934 X0 x sF4
       grind)
    | exact superpose eq1934 eq1779
    | exact resolve eq1779 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq2012 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1774 X0 x X0
       have i₂ := eq1934 X0 x sF0
       grind)
    | exact superpose eq1934 eq1774
    | exact resolve eq1774 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774 eq1934
  have eq2248 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 (M.op x y)))) = (τ (M.op X1 (M.op X1 (σ x)))) ∨ (τ (M.op X1 (M.op X1 (σ x)))) = (M.op x (τ (M.op X1 (M.op X1 (σ x))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1247 eq547
    | (have j0 := eq547 x (τ (M.op X1 (M.op X1 (σ x)))) x
       grind)
    | exact resolve eq547 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2309 : ∀ X1 : G, y = (τ (M.op X1 (M.op X1 (σ x)))) ∨ (τ (M.op X1 (M.op X1 (σ x)))) = (M.op x (τ (M.op X1 (M.op X1 (σ x))))) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq175 eq2248
    | (have j0 := eq2248 x X1
       grind)
    | exact resolve eq2248 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248
  have eq2323 : ∀ X1 : G, (M.op x y) = (τ (M.op X1 (M.op X1 (σ x)))) ∨ (τ (M.op X1 (M.op X1 (σ x)))) = (M.op x (τ (M.op X1 (M.op X1 (σ x))))) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq758 eq2309
    | (have j0 := eq2309 X1
       grind)
    | exact resolve eq2309 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309
  have eq2333 : ∀ X1 : G, (τ (M.op X1 (M.op X1 (σ x)))) = (M.op x (τ (M.op X1 (M.op X1 (σ x))))) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq2323 X1
       have j1 := eq1258 X1
       grind)
    | (have r₁ := eq2323 x
       have r₂ := eq1258 x
       grind)
    | exact resolve eq2323 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq2323
  have eq3039 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1214 eq540
    | exact resolve eq540 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq1214
  have eq3058 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3039
       have r₂ := eq1220
       grind)
    | exact resolve eq3039 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq3039
  have eq3247 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3058 eq153
    | exact resolve eq153 eq3058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq3058
  have eq3253 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq3247
    | exact resolve eq3247 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3247
  have eq3258 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq758 eq3253
    | exact resolve eq3253 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758 eq3253
  have eq3948 : ∀ X0 : G, (τ (M.op X0 (M.op X0 (σ x)))) ≠ (τ (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op (τ (M.op X0 (M.op X0 (σ x)))) (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (k x (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2333 eq12
    | (have j0 := eq12 x (τ (M.op X0 (M.op X0 (σ x))))
       grind)
    | (have r₁ := eq12 x (τ (M.op x (M.op x (σ x))))
       have r₂ := eq2333 x
       grind)
    | exact resolve eq12 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3950 : ∀ X0 : G, x = (M.op (τ (M.op X0 (M.op X0 (σ x)))) (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (k x (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3948 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948
  have eq3955 : ∀ X0 : G, x = (M.op (τ (M.op X0 (M.op X0 (σ x)))) (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1247 eq3950
    | (have j0 := eq3950 X0
       grind)
    | exact resolve eq3950 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3950
  have eq3956 : ∀ X0 : G, x = (M.op (τ (M.op X0 (M.op X0 (σ x)))) (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3955
  have eq4139 : ∀ X0 : G, (k x (τ (M.op X0 (M.op X0 (σ x))))) = (M.op x (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3956 eq178
    | exact resolve eq178 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq4154 : ∀ X0 : G, (M.op x y) = (M.op x (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1247 eq4139
    | exact resolve eq4139 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq4193 : ∀ X0 : G, (M.op x y) = (τ (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4154 eq2333
    | exact resolve eq2333 eq4154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333 eq4154
  have eq4200 : ∀ X0 : G, (M.op x y) = (τ (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193
  have eq4228 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4200 eq1247
    | exact resolve eq1247 eq4200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247 eq4200
  have eq4236 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq4228
  have eq4256 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4236 eq3258
    | exact resolve eq3258 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3258 eq4236
  have eq4272 : x = (M.op x y) := by grind
  clear eq4256
  have eq4277 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4272
       grind)
    | exact superpose eq4272 eq18
    | exact resolve eq18 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4278 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4272
       grind)
    | exact superpose eq4272 eq22
    | exact resolve eq22 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4279 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq4272
       grind)
    | exact superpose eq4272 eq36
    | exact resolve eq36 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq4281 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq4272
       grind)
    | exact superpose eq4272 eq175
    | exact resolve eq175 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq4284 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4278 eq20
    | exact resolve eq20 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4295 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq4278 eq365
    | exact resolve eq365 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq4794 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq4277 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | exact resolve eq12 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4797 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | exact superpose eq4277 eq177
    | exact resolve eq177 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4802 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4797 X0 x
       have i₂ := eq2012 x
       grind)
    | (have i₁ := eq4797 X0 x
       have i₂ := eq2012 X0
       grind)
    | exact superpose eq2012 eq4797
    | (have j0 := eq4797 X0 x
       grind)
    | exact resolve eq4797 eq2012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012 eq4797
  have eq4803 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have r₁ := eq4794
       have r₂ := eq759
       grind)
    | exact resolve eq4794 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4794
  have eq4805 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4802 X0
       have i₂ := eq4272
       grind)
    | exact superpose eq4272 eq4802
    | exact resolve eq4802 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4272 eq4802
  have eq4806 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq759 eq4803
    | exact resolve eq4803 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759 eq4803
  have eq5025 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 (M.op X0 (M.op X1 (M.op (M.op x y) (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq4281 eq177
    | exact resolve eq177 eq4281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5026 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4281 eq177
    | exact resolve eq177 eq4281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq5437 : (k (M.op x y) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq543 eq4295
    | exact resolve eq4295 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4295
  have eq5499 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq5437
    | exact resolve eq5437 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq5437
  have eq5519 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq584 eq5499
    | exact resolve eq5499 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5499
  have eq5739 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4806 eq41
    | exact resolve eq41 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4806
  have eq5743 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq5739
    | exact resolve eq5739 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5739
  have eq5749 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4284 eq5743
    | exact resolve eq5743 eq4284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5743
  have eq5762 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5749 eq543
    | exact resolve eq543 eq5749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq5749
  have eq5975 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5762 eq178
    | exact resolve eq178 eq5762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5991 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5519 eq5975
    | exact resolve eq5975 eq5519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5519 eq5975
  have eq5999 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5762 eq5991
    | exact resolve eq5991 eq5762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5762 eq5991
  have eq6001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5999 eq14
    | exact resolve eq14 eq5999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5999
  have eq6010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq6001
    | exact resolve eq6001 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6001
  have eq6013 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6010
       have r₂ := eq27
       grind)
    | exact resolve eq6010 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6010
  have eq6018 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6013
  have eq6560 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op X0 (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (k X0 (M.op X0 (M.op (M.op x y) (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq5025 X0 X0
       have i₂ := eq550 X0 sF0 sF0
       grind)
    | exact superpose eq550 eq5025
    | (have j1 := eq550 X0 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq5025 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq5025
  have eq6603 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (k X0 (M.op X0 (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq5026 eq6560
    | (have j0 := eq6560 X0
       grind)
    | exact resolve eq6560 eq5026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5026 eq6560
  have eq11211 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op X0 (M.op x y)))) = (k X1 (M.op X1 (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | exact superpose eq6603 eq16
    | (have j1 := eq6603 X1
       grind)
    | exact resolve eq16 eq6603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6603
  have eq11222 : ∀ X1 : G, y = (k X1 (M.op X1 (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op X1 y) := by
    intro X1
    first
    | exact superpose eq4281 eq11211
    | (have j0 := eq11211 x X1
       grind)
    | exact resolve eq11211 eq4281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281 eq11211
  have eq11252 : ∀ X0 : G, y = (k (M.op x y) (M.op X0 (M.op X0 (M.op x y)))) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq4805 eq11222
    | (have j0 := eq11222 (M.op x y)
       grind)
    | exact resolve eq11222 eq4805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4805
  have eq11272 : (σ y) = (k (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq11222 eq4279
    | (have j1 := eq11222 (M.op x y)
       grind)
    | exact resolve eq4279 eq11222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11222
  have eq11283 : (σ y) = (k (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq11272
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11272
    | exact resolve eq11272 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11272
  have eq11294 : ∀ X0 : G, y = (k (M.op x y) (M.op X0 (M.op X0 (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4277 eq11252
    | (have j0 := eq11252 X0
       grind)
    | exact resolve eq11252 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11252
  have eq11301 : (σ y) = (k (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4277 eq11283
    | exact resolve eq11283 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4277 eq11283
  have eq11326 : ∀ X0 : G, (σ y) = (k (σ x) (σ (M.op X0 (M.op X0 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11294 eq4279
    | exact resolve eq4279 eq11294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279 eq11294
  have eq11337 : ∀ X0 : G, (σ y) = (k (σ x) (σ (M.op X0 (M.op X0 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11326 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11326
    | (have j0 := eq11326 X0
       grind)
    | exact resolve eq11326 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11326
  have eq11362 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11301 eq547
    | (have j0 := eq547 (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) x
       grind)
    | exact resolve eq547 eq11301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11364 : (σ y) ≠ (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11301 eq559
    | (have j0 := eq559 (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))
       grind)
    | exact resolve eq559 eq11301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11366 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2010 eq11362
    | (have j0 := eq11362 (σ x)
       grind)
    | exact resolve eq11362 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11362
  have eq11372 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq584 eq11366
    | exact resolve eq11366 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11366
  have eq11378 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2010 eq11372
    | exact resolve eq11372 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11372
  have eq11381 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq584 eq11378
    | exact resolve eq11378 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11378
  have eq11382 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11381
    | exact resolve eq11381 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11381
  have eq11383 : (σ y) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq584 eq11382
    | exact resolve eq11382 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11382
  have eq11384 : (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11383
       have r₂ := eq11364
       grind)
    | exact resolve eq11383 eq11364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11364 eq11383
  have eq11409 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) = (σ (M.op X1 (M.op X1 (M.op x y)))) ∨ (σ (M.op X1 (M.op X1 (M.op x y)))) = (M.op (σ x) (σ (M.op X1 (M.op X1 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11337 eq547
    | (have j0 := eq547 (σ x) (σ (M.op X1 (M.op X1 (M.op x y)))) x
       grind)
    | exact resolve eq547 eq11337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq11411 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 (M.op X0 (M.op x y)))) ∨ (σ (M.op X0 (M.op X0 (M.op x y)))) = (M.op (σ x) (σ (M.op X0 (M.op X0 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11337 eq559
    | (have j0 := eq559 (σ x) (σ (M.op X0 (M.op X0 (M.op x y))))
       grind)
    | exact resolve eq559 eq11337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq11413 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (σ (M.op X1 (M.op X1 (M.op x y)))) ∨ (σ (M.op X1 (M.op X1 (M.op x y)))) = (M.op (σ x) (σ (M.op X1 (M.op X1 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq2010 eq11409
    | (have j0 := eq11409 (σ x) X1
       grind)
    | exact resolve eq11409 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11409
  have eq11422 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op X1 (M.op X1 (M.op x y)))) ∨ (σ (M.op X1 (M.op X1 (M.op x y)))) = (M.op (σ x) (σ (M.op X1 (M.op X1 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq584 eq11413
    | (have j0 := eq11413 X1
       grind)
    | exact resolve eq11413 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11413
  have eq11427 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op X1 (M.op X1 (M.op x y)))) ∨ (σ (M.op X1 (M.op X1 (M.op x y)))) = (M.op (σ x) (σ (M.op X1 (M.op X1 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq2010 eq11422
    | (have j0 := eq11422 X1
       grind)
    | exact resolve eq11422 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010 eq11422
  have eq11430 : ∀ X1 : G, (M.op (σ x) (σ y)) = (σ (M.op X1 (M.op X1 (M.op x y)))) ∨ (σ (M.op X1 (M.op X1 (M.op x y)))) = (M.op (σ x) (σ (M.op X1 (M.op X1 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq584 eq11427
    | (have j0 := eq11427 X1
       grind)
    | exact resolve eq11427 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11427
  have eq11431 : ∀ X1 : G, (M.op (σ x) (σ y)) = (σ (M.op X1 (M.op X1 (M.op x y)))) ∨ (σ (M.op X1 (M.op X1 (M.op x y)))) = (M.op (σ x) (σ (M.op X1 (M.op X1 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq26 eq11430
    | (have j0 := eq11430 X1
       grind)
    | exact resolve eq11430 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11430
  have eq11432 : ∀ X1 : G, (σ y) = (σ (M.op X1 (M.op X1 (M.op x y)))) ∨ (σ (M.op X1 (M.op X1 (M.op x y)))) = (M.op (σ x) (σ (M.op X1 (M.op X1 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq584 eq11431
    | (have j0 := eq11431 X1
       grind)
    | exact resolve eq11431 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq11431
  have eq11433 : ∀ X1 : G, (σ (M.op X1 (M.op X1 (M.op x y)))) = (M.op (σ x) (σ (M.op X1 (M.op X1 (M.op x y))))) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq11432 X1
       have j1 := eq11411 X1
       grind)
    | (have r₁ := eq11432 x
       have r₂ := eq11411 x
       grind)
    | exact resolve eq11432 eq11411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11411 eq11432
  have eq65826 : (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ≠ (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ (σ x) = (k (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11384 eq12
    | (have j0 := eq12 (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))
       have r₂ := eq11384
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11384
       grind)
    | exact resolve eq12 eq11384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11384
  have eq65835 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ (σ x) = (k (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by grind
  clear eq65826
  have eq65838 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11301 eq65835
    | exact resolve eq65835 eq11301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65835
  have eq65840 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq65838
       have r₂ := eq748
       grind)
    | exact resolve eq65838 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65838
  have eq66230 : (k (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq65840 eq178
    | exact resolve eq178 eq65840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq65840
  have eq66245 : (σ y) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11301 eq66230
    | exact resolve eq66230 eq11301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11301 eq66230
  have eq66342 : (σ y) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66245 eq11433
    | exact resolve eq11433 eq66245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11433 eq66245
  have eq66353 : (σ y) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) := by grind
  clear eq66342
  have eq66423 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66353 eq11337
    | exact resolve eq11337 eq66353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11337 eq66353
  have eq66566 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq66423
  have eq66629 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq801 eq66566
    | exact resolve eq66566 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801 eq66566
  have eq66671 : y = (M.op x y) := by
    first
    | (have r₁ := eq66629
       have r₂ := eq748
       grind)
    | exact resolve eq66629 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748 eq66629
  have eq66710 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq66671
       grind)
    | exact superpose eq66671 eq24
    | exact resolve eq24 eq66671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq66671
  have eq66861 : (σ x) = (σ y) := by
    first
    | exact superpose eq4278 eq66710
    | exact resolve eq66710 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278 eq66710
  have eq66939 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66861 eq6018
    | (have r₁ := eq6018
       have r₂ := eq66861
       grind)
    | exact resolve eq6018 eq66861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6018 eq66861
  have eq67019 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq66939
  have eq67189 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq67019 eq27
    | exact resolve eq27 eq67019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq67019
  have eq67208 : False := by grind
  exact eq67208

/-- `Equation575`: `x = y ◇ (z ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pyy_pxy_Equation575 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law575 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law575.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq44
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq44 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
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
  clear eq113 eq118
  have eq945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq103 eq71
    | (have j0 := eq71 (σ x) (σ y)
       grind)
    | exact resolve eq71 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq103
  have eq946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq945
    | exact resolve eq945 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq949 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq946
       have r₂ := eq27
       grind)
    | exact resolve eq946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq951 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq949
    | exact resolve eq949 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq961 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq951 eq14
    | exact resolve eq14 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq964 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f964_13 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op x x) := by
      intro X0
      grind
    have f964_20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
      intro X0 X1 X2
      grind
    have f964_23 : (M.op x y) ≠ (M.op x x) := by grind
    have f964_24 : (σ x) ≠ (σ y) := by grind
    have f964_26 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
      intro X0
      first
      | (have j0 := f964_13 X0
         grind)
      | (have r₁ := f964_13 X0
         have r₂ := f964_23
         grind)
      | exact resolve f964_13 f964_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f964_27 : (σ x) = (σ y) := by
      first
      | (have i₁ := f964_26 x
         have i₂ := f964_20 (σ y) (σ x) x
         grind)
      | exact superpose f964_20 f964_26
      | exact resolve f964_26 f964_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f964_28 : False := by
      first
      | (have r₁ := f964_27
         have r₂ := f964_24
         grind)
      | exact resolve f964_27 f964_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f964_28
  clear eq51 eq961
  have eq1025 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op X0 (M.op x y)))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq14
    | exact resolve eq14 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1028 : (σ x) = (σ y) ∨ x = y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f1028_13 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op X0 (M.op x y)))) ∨ (σ x) = (σ y) := by
      intro X0
      grind
    have f1028_20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
      intro X0 X1 X2
      grind
    have f1028_23 : (σ x) ≠ (σ y) := by grind
    have f1028_24 : x ≠ y := by grind
    have f1028_26 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
      intro X0
      first
      | (have j0 := f1028_13 X0
         grind)
      | (have r₁ := f1028_13 X0
         have r₂ := f1028_23
         grind)
      | exact resolve f1028_13 f1028_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1028_27 : x = y := by
      first
      | (have i₁ := f1028_26 x
         have i₂ := f1028_20 y x x
         grind)
      | exact superpose f1028_20 f1028_26
      | exact resolve f1028_26 f1028_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1028_28 : False := by
      first
      | (have r₁ := f1028_27
         have r₂ := f1028_24
         grind)
      | exact resolve f1028_27 f1028_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1028_28
  clear eq50 eq1025
  have eq1033 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1028 eq29
    | exact resolve eq29 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1028
  have eq1053 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq1033
    | exact resolve eq1033 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1033
  have eq1054 : x = y := by grind
  clear eq1053
  have eq1059 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1054
       grind)
    | exact superpose eq1054 eq18
    | exact resolve eq18 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1060 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1054
       grind)
    | exact superpose eq1054 eq24
    | exact resolve eq24 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1054
  have eq1080 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1060
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1060
    | exact resolve eq1060 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1060
  have eq1085 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1080 eq26
    | exact resolve eq26 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1080
  have eq1129 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1085 eq121
    | exact resolve eq121 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq1085
  have eq1143 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1129
       have i₂ := eq1059
       grind)
    | exact superpose eq1059 eq1129
    | exact resolve eq1129 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059 eq1129
  have eq1147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1143 eq15
    | exact resolve eq15 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1147
    | exact resolve eq1147 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1147
  have eq1173 : False := by grind
  exact eq1173
