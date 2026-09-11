import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_x_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) X1) X2 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq177 X0 x X2 X3
       have i₂ := eq16 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) X2) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X0) = (k X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X1) X1)
       have i₂ := eq16 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq1020 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X1) X2) = X0 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1030 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op (M.op X0 X2) X2)) ∨ (M.op X0 X0) = (M.op (M.op X0 X2) X2) ∨ (M.op (M.op X0 X2) X2) = (M.op (M.op (M.op X0 X2) X2) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (M.op (M.op X0 X1) X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 (M.op (M.op X0 X2) X2) (M.op (M.op X0 X2) X2)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq1039 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1020 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1128 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op (M.op X0 X2) X2)) ∨ (M.op (M.op X0 X2) X2) = (M.op (M.op (M.op X0 X2) X2) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1030 X0 X1 X2
       have j1 := eq184 X0 X2 X1
       grind)
    | (have r₁ := eq1030 X0 X1 X1
       have r₂ := eq184 X0 X1 X2
       grind)
    | exact resolve eq1030 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1138 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1105 X0 X1 X2
       have j1 := eq183 X0 X1 X2 X0
       grind)
    | (have r₁ := eq1105 X0 X1 X2
       have r₂ := eq183 X0 X1 X2 x
       grind)
    | exact resolve eq1105 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1105
  have eq1154 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X2) X2) ∨ (M.op X0 X0) = (k X1 (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1128 X0 X1 X2
       have i₂ := eq16 X0 X2 (M.op (M.op X0 X2) X2)
       grind)
    | exact superpose eq16 eq1128
    | (have j0 := eq1128 X0 X1 X2
       grind)
    | exact resolve eq1128 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1171 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1154 X0 X1 X2
       have j1 := eq184 X0 X2 X1
       grind)
    | (have r₁ := eq1154 X0 X1 X1
       have r₂ := eq184 X0 X1 X2
       grind)
    | exact resolve eq1154 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq1154
  have eq1279 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq1138
    | (have j0 := eq1138 (σ x) (σ y) X0
       grind)
    | exact resolve eq1138 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1304 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq182 X0 X0 x
       have i₂ := eq1138 X0 X0 x
       grind)
    | exact superpose eq1138 eq182
    | exact resolve eq182 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1309 : ∀ X0 X2 X3 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq182 (M.op (M.op X0 x) x) X2 X3
       have i₂ := eq1138 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq1138 eq182
    | exact resolve eq182 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1401 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1304 X0
       grind)
    | exact superpose eq1304 eq13
    | exact resolve eq13 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2132 : ∀ X0 X1 X2 X3 : G, (k X1 X1) = (M.op (k X0 (M.op (M.op (k X1 X1) X2) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1309 X1 (k X1 X1) X3
       have i₂ := eq1171 (k X1 X1) X0 X2
       grind)
    | exact superpose eq1171 eq1309
    | exact resolve eq1309 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq2180 : ∀ X0 X1 X3 : G, (k X1 X1) = (M.op (k X0 (k X1 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2132 X0 X1 x X3
       have i₂ := eq1309 X1 x x
       grind)
    | exact superpose eq1309 eq2132
    | exact resolve eq2132 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309 eq2132
  have eq3550 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1038
       grind)
    | exact superpose eq1038 eq39
    | exact resolve eq39 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq3551 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3550
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3550
    | exact resolve eq3550 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3550
  have eq3553 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3551
    | exact resolve eq3551 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3551
  have eq3555 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3553
       have i₂ := eq1304 x
       grind)
    | exact superpose eq1304 eq3553
    | exact resolve eq3553 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq11944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3555 eq1039
    | exact resolve eq1039 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039 eq3555
  have eq11953 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11944
       have r₂ := eq27
       grind)
    | exact resolve eq11944 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11944
  have eq11958 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11953
       have i₂ := eq1304 sF2
       grind)
    | exact superpose eq1304 eq11953
    | exact resolve eq11953 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq11953
  have eq11972 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11958 eq141
    | exact resolve eq141 eq11958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11958
  have eq11995 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq11972
    | exact resolve eq11972 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11972
  have eq11996 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11995
  have eq12018 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq11996
       grind)
    | exact superpose eq11996 eq39
    | exact resolve eq39 eq11996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq12023 : ∀ X0 : G, x ≠ x ∨ x = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1401 x x
       have i₂ := eq11996
       grind)
    | exact superpose eq11996 eq1401
    | (have r₁ := eq1401 x x
       have r₂ := eq11996
       grind)
    | exact resolve eq1401 eq11996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11996
  have eq12035 : ∀ X0 : G, x = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12023 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12023
  have eq12041 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12018
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12018
    | exact resolve eq12018 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12018
  have eq12064 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq12035 (τ X0)
       grind)
    | exact superpose eq12035 eq34
    | exact resolve eq34 eq12035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12035
  have eq12089 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12064 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12064
    | (have j0 := eq12064 X0
       grind)
    | exact resolve eq12064 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12064
  have eq12123 : ∀ X0 X1 : G, (σ x) = (M.op (k X0 (σ x)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12041 eq2180
    | exact resolve eq2180 eq12041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12041
  have eq12132 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq12089 eq12123
    | exact resolve eq12123 eq12089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12089 eq12123
  have eq13781 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12132 eq26
    | (have j1 := eq12132 (σ y)
       grind)
    | exact resolve eq26 eq12132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12132
  have eq13825 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13781
  have eq13885 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13825 eq1279
    | exact resolve eq1279 eq13825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq13908 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq13885
    | (have j0 := eq13885 X0
       grind)
    | exact resolve eq13885 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13885
  have eq13941 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13825 eq13908
    | exact resolve eq13908 eq13825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13908
  have eq14258 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13941 eq26
    | (have j1 := eq13941 (σ y)
       grind)
    | exact resolve eq26 eq13941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13941
  have eq14325 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13825 eq14258
    | exact resolve eq14258 eq13825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13825 eq14258
  have eq14371 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14325 eq141
    | exact resolve eq141 eq14325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq14376 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14325 eq1401
    | (have r₁ := eq1401 (σ x) x
       have r₂ := eq14325
       grind)
    | exact resolve eq1401 eq14325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14325
  have eq14390 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14376
  have eq14403 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq14371
    | exact resolve eq14371 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14371
  have eq14456 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14390 eq389
    | exact resolve eq389 eq14390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq14390
  have eq14507 : ∀ X0 : G, x = (k X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq14456
    | exact resolve eq14456 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14456
  have eq14558 : ∀ X0 X1 : G, x = (M.op (k X0 x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2180 X0 x x
       have i₂ := eq14403
       grind)
    | exact superpose eq14403 eq2180
    | exact resolve eq2180 eq14403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14403
  have eq14572 : ∀ X1 : G, x = (M.op x X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq14507 eq14558
    | exact resolve eq14558 eq14507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14507 eq14558
  have eq14772 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14572 y
       grind)
    | exact superpose eq14572 eq18
    | (have j1 := eq14572 y
       grind)
    | exact resolve eq18 eq14572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14572
  have eq14816 : x = (M.op x y) := by grind
  clear eq14772
  have eq14852 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14816
       grind)
    | exact superpose eq14816 eq18
    | exact resolve eq18 eq14816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14853 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq14816
       grind)
    | exact superpose eq14816 eq22
    | exact resolve eq22 eq14816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14816
  have eq14941 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14853 eq20
    | exact resolve eq20 eq14853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14853
  have eq15080 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq14852 eq1138
    | exact resolve eq1138 eq14852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq15098 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq14852 eq15080
    | exact resolve eq15080 eq14852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15080
  have eq15344 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq15098 eq14852
    | exact resolve eq14852 eq15098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14852 eq15098
  have eq16470 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15344 eq37
    | exact resolve eq37 eq15344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq16476 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq15344 eq1401
    | (have r₁ := eq1401 (M.op x y) x
       have r₂ := eq15344
       grind)
    | exact resolve eq1401 eq15344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401 eq15344
  have eq16490 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq16476 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16476
  have eq16506 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16470
    | exact resolve eq16470 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16470
  have eq16518 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14941 eq16506
    | exact resolve eq16506 eq14941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16506
  have eq16554 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq16490 eq34
    | exact resolve eq34 eq16490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq16490
  have eq16589 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq16554
    | (have j0 := eq16554 X0
       grind)
    | exact resolve eq16554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq16554
  have eq16607 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq14941 eq16589
    | exact resolve eq16589 eq14941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16589
  have eq16649 : ∀ X0 X1 : G, (σ x) = (M.op (k X0 (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq16518 eq2180
    | exact resolve eq2180 eq16518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180 eq16518
  have eq16661 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | exact superpose eq16607 eq16649
    | exact resolve eq16649 eq16607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16607 eq16649
  have eq16816 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16661 eq26
    | (have j1 := eq16661 (σ y)
       grind)
    | exact resolve eq26 eq16661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq16661
  have eq16939 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq16816 eq27
    | exact resolve eq27 eq16816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16816
  have eq17007 : False := by grind
  exact eq17007

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation4075 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq93 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq98 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq94
  have eq99 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq106
    | exact resolve eq106 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1695 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq74
  have eq1743 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1695 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq13082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq13082
    | exact resolve eq13082 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13082
  have eq13094 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq13083
       have r₂ := eq28
       grind)
    | exact resolve eq13083 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13083
  have eq13098 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq13094
    | exact resolve eq13094 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13094
  have eq13107 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13098 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13098
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13098
       grind)
    | exact resolve eq12 eq13098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13098
  have eq147967 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq13107
    | (have j0 := eq13107 (σ x)
       grind)
    | (have r₁ := eq13107 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq13107 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13107
  have eq147974 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq147967
  have eq147975 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq147974
  have eq148102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq147975 eq108
    | exact resolve eq108 eq147975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq147975
  have eq148119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq148102
  have eq148126 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq148119
       have r₂ := eq28
       grind)
    | exact resolve eq148119 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148119
  have eq148131 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq148126
       grind)
    | exact superpose eq148126 eq99
    | exact resolve eq99 eq148126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148140 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k y X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq148126
       grind)
    | exact superpose eq148126 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq148126
       grind)
    | exact resolve eq12 eq148126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148126
  have eq148313 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq148131
    | exact resolve eq148131 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148131
  have eq481110 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq148140 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq148140
    | (have j0 := eq148140 x
       grind)
    | (have r₁ := eq148140 x
       have r₂ := eq19
       grind)
    | exact resolve eq148140 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148140
  have eq481125 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq481110
  have eq481126 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq481125
  have eq481368 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1743 x y
       have i₂ := eq481126
       grind)
    | exact superpose eq481126 eq1743
    | (have j0 := eq1743 x y
       grind)
    | exact resolve eq1743 eq481126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743 eq481126
  have eq481379 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq481368
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq481368
    | exact resolve eq481368 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481368
  have eq481401 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq481379
    | exact resolve eq481379 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481379
  have eq481410 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq481401
       have r₂ := eq148313
       grind)
    | exact resolve eq481401 eq148313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481401
  have eq481415 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq481410
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq481410
    | exact resolve eq481410 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq481410
  have eq481420 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq481415
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq481415
    | exact resolve eq481415 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481415
  have eq481425 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq481420
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq481420
    | exact resolve eq481420 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481420
  have eq481429 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq481425
    | exact resolve eq481425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481425
  have eq481433 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq481429
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq481429
    | exact resolve eq481429 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481429
  have eq481437 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq481433
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq481433
    | exact resolve eq481433 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481433
  have eq481438 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq481437
  have eq481573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq481438 eq148313
    | exact resolve eq148313 eq481438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148313 eq481438
  have eq481827 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq481573
  have eq481959 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq481827
       have r₂ := eq28
       grind)
    | exact resolve eq481827 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481827
  have eq482104 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq481959 eq30
    | exact resolve eq30 eq481959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq481959
  have eq482253 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq482104
    | exact resolve eq482104 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq482104
  have eq482254 : x = y := by grind
  clear eq482253
  have eq482274 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq482254
       grind)
    | exact superpose eq482254 eq19
    | exact resolve eq19 eq482254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq482275 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq482254
       grind)
    | exact superpose eq482254 eq25
    | exact resolve eq25 eq482254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq482254
  have eq482548 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq482275
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq482275
    | exact resolve eq482275 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq482275
  have eq482581 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq482548 eq27
    | exact resolve eq27 eq482548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq482548
  have eq483146 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq482581 eq73
    | exact resolve eq73 eq482581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq482581
  have eq483411 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq483146
       have i₂ := eq482274
       grind)
    | exact superpose eq482274 eq483146
    | exact resolve eq483146 eq482274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482274 eq483146
  have eq485592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq483411 eq15
    | exact resolve eq15 eq483411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483411
  have eq485903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq485592
    | exact resolve eq485592 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq485592
  have eq486003 : False := by grind
  exact eq486003

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_y_pyx_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
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
  clear eq24 eq35
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
  have eq60 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X2) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 (M.op X0 X1) x x X4
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ X0 ∨ (k X0 X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X0 X4
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X4
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq86 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq93 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq86
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq217 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq63 eq14
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ (M.op (M.op X0 X0) X6) ∨ (k (M.op (M.op (M.op X0 X1) X2) X3) X7) = X7 := by
    intro X0 X1 X2 X3 X6 X7
    first
    | (have i₁ := eq68 (M.op (M.op (M.op X0 X1) X2) X3) x x X6 X7
       have i₂ := eq60 X0 X1 X2 X3 x x
       grind)
    | exact superpose eq60 eq68
    | (have j0 := eq68 (M.op (M.op (M.op X0 X1) X2) X3) X1 X2 X3 X7
       grind)
    | exact resolve eq68 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1523 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq80 X0 X0
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq80 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq80 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1534 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1535 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1534 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1537 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1523 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1547 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1537 X0 X1
       have j1 := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq1537 X0 X1
       have r₂ := eq13 (σ X0) X1
       grind)
    | exact resolve eq1537 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq1662 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1547 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1547
    | (have j0 := eq1547 (τ X0) X1
       grind)
    | exact resolve eq1547 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1547
  have eq1670 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1662 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1662
    | (have j0 := eq1662 X0 X1
       grind)
    | exact resolve eq1662 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662
  have eq1676 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1670 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1670
    | (have j0 := eq1670 X0 X1
       grind)
    | exact resolve eq1670 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq7696 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq7721 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49 eq7696
    | exact resolve eq7696 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7696
  have eq7750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq7751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq7750
    | exact resolve eq7750 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7750
  have eq7762 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq7751
       have r₂ := eq27
       grind)
    | exact resolve eq7751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7751
  have eq7764 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq7762
    | exact resolve eq7762 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7762
  have eq7768 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq7764 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq7764
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq7764
       grind)
    | exact resolve eq13 eq7764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7764
  have eq7789 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7768
  have eq7813 : ∀ X0 X1 : G, x ≠ x ∨ (k x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq7789 X1
       grind)
    | exact superpose eq7789 eq13
    | (have j0 := eq13 x X0
       have j1 := eq7789 X1
       grind)
    | (have r₁ := eq13 x X1
       have r₂ := eq7789 X0
       grind)
    | exact resolve eq13 eq7789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7789
  have eq7834 : ∀ X0 X1 : G, (k (σ x) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k x X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7813 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7813
  have eq7936 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq7834 (k sF2 sF2) x
       grind)
    | exact superpose eq7834 eq49
    | (have j1 := eq7834 X0 x
       grind)
    | exact resolve eq49 eq7834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7834
  have eq7979 : ∀ X0 : G, x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k x X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq7936
    | (have j0 := eq7936 x
       grind)
    | exact resolve eq7936 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7936
  have eq8011 : ∀ X0 : G, (k x X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7979 X0
       have j1 := eq1676 x X0
       grind)
    | (have r₁ := eq7979 X0
       have r₂ := eq1676 x x
       grind)
    | (have r₁ := eq7979 x
       have r₂ := eq1676 x x
       grind)
    | exact resolve eq7979 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676 eq7979
  have eq8057 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7721
       have i₂ := eq8011 x
       grind)
    | exact superpose eq8011 eq7721
    | exact resolve eq7721 eq8011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7721 eq8011
  have eq8072 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8057
  have eq8133 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq217 X0
       have i₂ := eq8072
       grind)
    | exact superpose eq8072 eq217
    | exact resolve eq217 eq8072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8143 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60 x x X2 X3 x x
       have i₂ := eq8072
       grind)
    | exact superpose eq8072 eq60
    | exact resolve eq60 eq8072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8072
  have eq8164 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X3
    first
    | (have i₁ := eq8143 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq8143
    | exact resolve eq8143 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8143
  have eq8173 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8164 x
       have i₂ := eq217 x
       grind)
    | exact superpose eq217 eq8164
    | exact resolve eq8164 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8164
  have eq8956 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8133 eq8173
    | exact resolve eq8173 eq8133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8133 eq8173
  have eq9001 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8956 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8956
  have eq9068 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9001 y
       grind)
    | exact superpose eq9001 eq18
    | (have j1 := eq9001 y
       grind)
    | exact resolve eq18 eq9001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9001
  have eq9099 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9068
  have eq9127 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq9099 eq64
    | exact resolve eq64 eq9099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq9611 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq9127
    | (have j0 := eq9127 (σ y) X0
       grind)
    | exact resolve eq9127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9127
  have eq9735 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9099 eq9611
    | exact resolve eq9611 eq9099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9611
  have eq9772 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9735 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9735
  have eq9861 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9772
    | (have j0 := eq9772 (σ y)
       grind)
    | exact resolve eq9772 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9772
  have eq9962 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9861 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | exact resolve eq13 eq9861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9861
  have eq10012 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9962 X0
       grind)
    | (have r₁ := eq9962 X0
       have r₂ := eq9099
       grind)
    | exact resolve eq9962 eq9099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9099 eq9962
  have eq10258 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10012 eq49
    | exact resolve eq49 eq10012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq10012
  have eq10303 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq10258
    | exact resolve eq10258 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10258
  have eq10766 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq10303
       grind)
    | exact superpose eq10303 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq10303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10303
  have eq10767 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq10766
  have eq11063 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq217 X0
       have i₂ := eq10767
       grind)
    | exact superpose eq10767 eq217
    | exact resolve eq217 eq10767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11073 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60 x x X2 X3 x x
       have i₂ := eq10767
       grind)
    | exact superpose eq10767 eq60
    | exact resolve eq60 eq10767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq10767
  have eq11094 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) := by
    intro X3
    first
    | (have i₁ := eq11073 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq11073
    | exact resolve eq11073 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11073
  have eq11103 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11094 x
       have i₂ := eq217 x
       grind)
    | exact superpose eq217 eq11094
    | exact resolve eq11094 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11094
  have eq16151 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11063 eq11103
    | exact resolve eq11103 eq11063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11063 eq11103
  have eq16210 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq16151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16151
  have eq16295 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16210 y
       grind)
    | exact superpose eq16210 eq18
    | (have j1 := eq16210 y
       grind)
    | exact resolve eq18 eq16210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16210
  have eq16332 : x = (M.op x y) := by grind
  clear eq16295
  have eq16362 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16332 eq20
    | exact resolve eq20 eq16332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq16365 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq16332 eq63
    | exact resolve eq63 eq16332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq16469 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16362
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16362
    | exact resolve eq16362 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16362
  have eq16645 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op (M.op x X0) X1) X2) ∨ (k (M.op (M.op (M.op x X0) X1) X2) X4) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq752 x X0 X1 X2 x X4
       have i₂ := eq217 x
       grind)
    | exact superpose eq217 eq752
    | (have j0 := eq752 x X0 X1 X2 x X4
       grind)
    | exact resolve eq752 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq752
  have eq16682 : ∀ X0 X1 X2 X4 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op (M.op (M.op x X0) X1) X2) X4) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16645 X0 X1 X2 X4
       have i₂ := eq14 x X0 X1 X2
       grind)
    | exact superpose eq14 eq16645
    | (have j0 := eq16645 X0 X1 X2 X4
       grind)
    | exact resolve eq16645 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16645
  have eq16767 : ∀ X0 X1 X2 X4 : G, (M.op x x) ≠ (M.op x x) ∨ (k (M.op (M.op (M.op x X0) X1) X2) X4) = X4 := by
    intro X0 X1 X2 X4
    first
    | exact superpose eq16332 eq16682
    | (have j0 := eq16682 X0 X1 X2 X4
       grind)
    | exact resolve eq16682 eq16332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16682
  have eq16768 : ∀ X0 X1 X2 X4 : G, (k (M.op (M.op (M.op x X0) X1) X2) X4) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have j0 := eq16767 X0 X1 X2 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16767
  have eq16828 : ∀ X4 : G, (k (M.op x x) X4) = X4 := by
    intro X4
    first
    | (have i₁ := eq16768 x x x X4
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq16768
    | exact resolve eq16768 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16768
  have eq16918 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16469 eq26
    | exact resolve eq26 eq16469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq19054 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16365 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16365
    | (have j0 := eq16365 y X0
       grind)
    | exact resolve eq16365 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16365
  have eq19183 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq16332 eq19054
    | exact resolve eq19054 eq16332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19054
  have eq20020 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq19183 y
       grind)
    | exact superpose eq19183 eq18
    | (have j1 := eq19183 y
       grind)
    | exact resolve eq18 eq19183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19183
  have eq20053 : x = (M.op x x) := by
    first
    | exact superpose eq16332 eq20020
    | exact resolve eq20020 eq16332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16332 eq20020
  have eq20085 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16828 X0
       have i₂ := eq20053
       grind)
    | exact superpose eq20053 eq16828
    | exact resolve eq16828 eq20053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16828 eq20053
  have eq21021 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1535 x
       have i₂ := eq20085 x
       grind)
    | exact superpose eq20085 eq1535
    | (have j0 := eq1535 x
       grind)
    | exact resolve eq1535 eq20085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535 eq20085
  have eq21085 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21021
  have eq21136 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21085
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21085
    | exact resolve eq21085 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21085
  have eq21183 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16469 eq21136
    | exact resolve eq21136 eq16469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16469 eq21136
  have eq21860 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq21183 eq65
    | exact resolve eq65 eq21183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq21886 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq21183 eq21860
    | exact resolve eq21860 eq21183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21183 eq21860
  have eq22397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21886 eq16918
    | exact resolve eq16918 eq21886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16918 eq21886
  have eq22458 : False := by grind
  exact eq22458

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_x_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
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
  have eq125 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq36 (M.op x x)
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq36
    | exact resolve eq36 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq179 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq37 (M.op y y)
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq37
    | exact resolve eq37 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq180 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq38 (M.op sF0 sF0)
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq38
    | exact resolve eq38 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq181 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq180
    | exact resolve eq180 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq182 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq179
    | exact resolve eq179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq183 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq178
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq178
    | exact resolve eq178 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq191 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq202 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq191
    | exact resolve eq191 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq209 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq338 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq694 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op (M.op (M.op X0 X1) X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq175 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq706 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ X3 ∨ (k X3 (M.op (M.op X0 X1) X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X3 (M.op (M.op X0 X1) X2)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq28
    | (have j0 := eq28 X3 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq28 (M.op X0 X0) (M.op (M.op X0 X1) X2)
       have r₂ := eq16 X0 X1 X2 (M.op X0 X0)
       grind)
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq694 eq16
    | exact resolve eq16 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X2) := by
    intro X2
    first
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq792 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq11
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq799 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (k X0 X1) X2) X3) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X0 X2 X3
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq800 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq844 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq792 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq1045 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq696 X0 x X2
       have i₂ := eq696 X0 x X1
       grind)
    | (have i₁ := eq696 X0 X0 x
       have i₂ := eq696 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq696 eq696
    | exact resolve eq696 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq719 x
       have i₂ := eq696 sF2 x x
       grind)
    | (have i₁ := eq719 (M.op sF2 sF2)
       have i₂ := eq696 sF2 sF2 x
       grind)
    | exact superpose eq696 eq719
    | exact resolve eq719 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq1243 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq798
       grind)
    | exact superpose eq798 eq40
    | exact resolve eq40 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1244 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1243
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1243
    | exact resolve eq1243 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1246 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1244
    | exact resolve eq1244 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1246 eq799
    | exact resolve eq799 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1261 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1254
       have r₂ := eq27
       grind)
    | exact resolve eq1254 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1266 : y = (k y (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1261 eq220
    | exact resolve eq220 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq1261
  have eq1280 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq1266
    | exact resolve eq1266 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq1283 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1280
       have r₂ := eq176
       grind)
    | exact resolve eq1280 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq1280
  have eq1284 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1283
       have r₂ := eq13 y x
       grind)
    | exact resolve eq1283 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1288 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1284
       grind)
    | exact superpose eq1284 eq40
    | exact resolve eq40 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1291 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1288
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1288
    | exact resolve eq1288 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1293 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq1291
       have r₂ := eq177
       grind)
    | exact resolve eq1291 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1291
  have eq1298 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1293 eq799
    | exact resolve eq799 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq1301 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | exact superpose eq1293 eq142
    | exact resolve eq142 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1293
  have eq1302 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1298
  have eq1304 : y = (k y x) := by
    first
    | exact superpose eq32 eq1301
    | exact resolve eq1301 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1309 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq798
       have i₂ := eq1304
       grind)
    | exact superpose eq1304 eq798
    | exact resolve eq798 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq1312 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1309
  have eq1319 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1302 eq1045
    | exact resolve eq1045 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1320 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) X1) (M.op (σ y) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1302 eq696
    | exact resolve eq696 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1323 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1302 eq696
    | exact resolve eq696 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1302 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1327 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1302 eq28
    | (have j0 := eq28 (σ y) (σ y)
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq1302
       grind)
    | exact resolve eq28 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1328 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1324
  have eq1335 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1045 y X1 x
       have i₂ := eq1312
       grind)
    | exact superpose eq1312 eq1045
    | exact resolve eq1045 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1339 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq696 y y x
       have i₂ := eq1312
       grind)
    | exact superpose eq1312 eq696
    | exact resolve eq696 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1342 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y y x x
       have i₂ := eq1312
       grind)
    | exact superpose eq1312 eq16
    | exact resolve eq16 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1375 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1319 eq26
    | (have j1 := eq1319 (σ y) X0
       grind)
    | exact resolve eq26 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1381 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1319 eq202
    | exact resolve eq202 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1415 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1375 eq202
    | exact resolve eq202 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1493 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1323 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1511 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1493 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1524 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1375 eq1511
    | (have j0 := eq1511 (σ y)
       grind)
    | exact resolve eq1511 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1637 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq1335 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq1335 X0 y
       grind)
    | exact superpose eq1335 eq18
    | (have j1 := eq1335 y X0
       grind)
    | exact resolve eq18 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1642 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq709 X1
       have i₂ := eq1335 x X0
       grind)
    | (have i₁ := eq709 X1
       have i₂ := eq1335 X0 x
       grind)
    | exact superpose eq1335 eq709
    | exact resolve eq709 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq1335
  have eq1661 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1342 eq1642
    | (have j1 := eq1342 y (M.op x y)
       grind)
    | exact resolve eq1642 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq1677 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183
       have i₂ := eq1637 x
       grind)
    | exact superpose eq1637 eq183
    | exact resolve eq183 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1684 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1637 x
       grind)
    | exact superpose eq1637 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq1637 x
       grind)
    | exact resolve eq13 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1696 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1677
    | exact resolve eq1677 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq1697 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1661
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq1661
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1661 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1701 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1661 eq181
    | exact resolve eq181 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1710 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1661 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1713 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1661 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq1661
       grind)
    | exact resolve eq28 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661
  have eq1714 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1710
  have eq1715 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq1697
  have eq1719 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1701
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1701
    | exact resolve eq1701 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701
  have eq1773 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11 x x
       have i₂ := eq1339 X0
       grind)
    | (have i₁ := eq11 X0 x
       have i₂ := eq1339 X0
       grind)
    | exact superpose eq1339 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq1791 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1773 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773
  have eq1804 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1637 eq1791
    | (have j0 := eq1791 y
       grind)
    | exact resolve eq1791 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791
  have eq1811 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1637 eq1804
    | (have j0 := eq1804 y
       grind)
    | exact resolve eq1804 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637 eq1804
  have eq2400 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1328 eq116
    | exact resolve eq116 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1328
  have eq2407 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq2400
    | exact resolve eq2400 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400
  have eq2479 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1811
       grind)
    | exact superpose eq1811 eq40
    | exact resolve eq40 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2482 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2479
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2479
    | exact resolve eq2479 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2484 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2482
    | exact resolve eq2482 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq3254 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1524 eq2484
    | (have j1 := eq1524 X0
       grind)
    | exact resolve eq2484 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq3263 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3254 X0
       grind)
    | (have r₁ := eq3254 X0
       have r₂ := eq27
       grind)
    | exact resolve eq3254 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254
  have eq3542 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1715 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq28 (M.op x y) (M.op x y)
       have r₂ := eq1715
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq1715
       grind)
    | exact resolve eq28 eq1715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1715
  have eq3550 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq3542
  have eq3610 : x ≠ x ∨ x = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1415 eq828
    | (have j0 := eq828 (τ (M.op (σ x) (σ y))) x
       grind)
    | (have r₁ := eq828 (τ (M.op (σ x) (σ y))) x
       have r₂ := eq1415
       grind)
    | exact resolve eq828 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq3636 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1719 eq828
    | (have j0 := eq828 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq828 (σ x) (σ (M.op x y))
       have r₂ := eq1719
       grind)
    | exact resolve eq828 eq1719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq3642 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1696 eq828
    | (have j0 := eq828 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq828 (σ (M.op x y)) (σ x)
       have r₂ := eq1696
       grind)
    | exact resolve eq828 eq1696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq3683 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3642
  have eq3689 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq3636
  have eq3715 : x = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3610
  have eq3842 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq3550
  have eq3847 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3842
       have r₂ := eq1714
       grind)
    | exact resolve eq3842 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3842
  have eq3854 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3847 eq42
    | exact resolve eq42 eq3847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3847
  have eq3861 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq3854
    | exact resolve eq3854 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3854
  have eq3863 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3861
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3861
    | exact resolve eq3861 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3861
  have eq3872 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3863 eq828
    | (have j0 := eq828 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq828 eq3863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3873 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq3872
  have eq3969 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq843 X0 x x x
       grind)
    | exact superpose eq843 eq16
    | (have j1 := eq843 X0 x x x
       grind)
    | exact resolve eq16 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq4243 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (M.op (σ x) X0) X1)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3683 eq699
    | exact resolve eq699 eq3683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq3683
  have eq4251 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (M.op (σ x) X0) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq4243 X0 X1
       have j1 := eq706 (σ x) X0 X1 (σ (M.op x y))
       grind)
    | (have r₁ := eq4243 X0 X1
       have r₂ := eq706 (σ x) X1 x (σ (M.op x y))
       grind)
    | exact resolve eq4243 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq4243
  have eq4255 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq4251
    | (have j0 := eq4251 (σ y) X0
       grind)
    | exact resolve eq4251 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4251
  have eq4292 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (M.op x y) (τ (M.op (M.op (σ x) (σ y)) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4255 eq125
    | exact resolve eq125 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq4255
  have eq4296 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op (M.op (σ x) (σ y)) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq4292
    | exact resolve eq4292 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4292
  have eq4329 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3689 eq1045
    | exact resolve eq1045 eq3689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3689
  have eq4414 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1320 eq1375
    | (have j1 := eq1320 (σ y) X0
       grind)
    | exact resolve eq1375 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4469 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4414 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4414
  have eq5640 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3263 eq1381
    | exact resolve eq1381 eq3263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3263
  have eq5669 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5640
  have eq5699 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq5669
    | exact resolve eq5669 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5669
  have eq5719 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1684 x
       grind)
    | (have r₁ := eq5699
       have r₂ := eq1684 y
       grind)
    | (have r₁ := eq5699
       have r₂ := eq1684 x
       grind)
    | exact resolve eq5699 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684 eq5699
  have eq5733 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1811
       have i₂ := eq5719
       grind)
    | exact superpose eq5719 eq1811
    | exact resolve eq1811 eq5719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5736 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq5719
       grind)
    | exact superpose eq5719 eq40
    | exact resolve eq40 eq5719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5719
  have eq5744 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5733
  have eq5756 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5736
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5736
    | exact resolve eq5736 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5736
  have eq5761 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5744 eq27
    | exact resolve eq27 eq5744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5771 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op (σ y) X0))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5744 eq4296
    | exact resolve eq4296 eq5744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296
  have eq5776 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op (σ y) X0))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5771
  have eq5795 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5756 eq828
    | (have j0 := eq828 (σ x) (σ x)
       grind)
    | (have r₁ := eq828 (σ x) (σ x)
       have r₂ := eq5756
       grind)
    | exact resolve eq828 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq5796 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5795
  have eq5797 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5796
  have eq5935 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5797 eq1375
    | exact resolve eq1375 eq5797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375 eq5797
  have eq5969 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5935
  have eq6082 : ∀ X0 X2 X3 : G, (k (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ y) X0) (M.op (σ y) X0)) X2) X3) ∨ (σ x) = (M.op (M.op (M.op (M.op (σ y) X0) (M.op (σ y) X0)) X2) X3) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X2 X3
    first
    | exact superpose eq1320 eq844
    | exact resolve eq844 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq1320
  have eq6241 : ∀ X0 X2 X3 : G, (k (σ x) (σ x)) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) ∨ (σ x) = (M.op (M.op (M.op (M.op (σ y) X0) (M.op (σ y) X0)) X2) X3) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6082 X0 X2 X3
       have i₂ := eq16 (M.op sF3 X0) (M.op sF3 X0) X2 X3
       grind)
    | exact superpose eq16 eq6082
    | (have j0 := eq6082 X0 X2 X3
       grind)
    | exact resolve eq6082 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6082
  have eq6298 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) ∨ (k (σ x) (σ x)) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6241 X0 x x
       have i₂ := eq16 (M.op sF3 X0) (M.op sF3 X0) x x
       grind)
    | exact superpose eq16 eq6241
    | (have j0 := eq6241 X0 x x
       grind)
    | exact resolve eq6241 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6241
  have eq6330 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4469 eq6298
    | (have j0 := eq6298 X0
       grind)
    | exact resolve eq6298 eq4469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6298
  have eq6341 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4469 eq6330
    | exact resolve eq6330 eq4469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4469 eq6330
  have eq6423 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq804 y y X0 X1
       have i₂ := eq2407
       grind)
    | exact superpose eq2407 eq804
    | (have j0 := eq804 y y x x
       grind)
    | exact resolve eq804 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6442 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) X0) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3863 eq804
    | (have j0 := eq804 (σ (M.op x y)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq804 eq3863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6606 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) X0) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq6442 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6442
  have eq6612 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq6423 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6423
  have eq6682 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) X0) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3969 eq6606
    | (have j1 := eq3969 (σ (M.op x y))
       grind)
    | exact resolve eq6606 eq3969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6606
  have eq6691 : ∀ X0 X1 : G, (k y y) = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq3969 eq6612
    | (have j1 := eq3969 y
       grind)
    | exact resolve eq6612 eq3969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6612
  have eq6746 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3863 eq6682
    | exact resolve eq6682 eq3863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6682
  have eq6753 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq2407 eq6691
    | exact resolve eq6691 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6691
  have eq6779 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1342 eq6753
    | (have j0 := eq6753 X0 X1
       have j1 := eq1342 X0 X1
       grind)
    | exact resolve eq6753 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342 eq6753
  have eq9151 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4329 eq26
    | (have j1 := eq4329 (σ y) X0
       grind)
    | exact resolve eq26 eq4329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4329
  have eq10355 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9151 eq3969
    | exact resolve eq3969 eq9151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9151
  have eq10732 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5969 eq10355
    | exact resolve eq10355 eq5969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5969 eq10355
  have eq11618 : ∀ X1 X2 : G, (M.op (σ x) X1) = (M.op (σ x) X2) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X1 X2
    first
    | exact superpose eq6746 eq1045
    | exact resolve eq1045 eq6746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746
  have eq13802 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11618 eq26
    | (have j1 := eq11618 (σ y) X0
       grind)
    | exact resolve eq26 eq11618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11618
  have eq16778 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10732 eq2484
    | exact resolve eq2484 eq10732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2484 eq10732
  have eq16803 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq16778
  have eq16819 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq16803
       have r₂ := eq5761
       grind)
    | exact resolve eq16803 eq5761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5761 eq16803
  have eq16831 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5744 eq16819
    | exact resolve eq16819 eq5744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16819
  have eq16857 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16831 eq1055
    | exact resolve eq1055 eq16831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq16888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16831 eq13802
    | exact resolve eq13802 eq16831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13802 eq16831
  have eq16906 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq16888
  have eq16946 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16906
       have r₂ := eq27
       grind)
    | exact resolve eq16906 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16906
  have eq16947 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5744 eq16857
    | exact resolve eq16857 eq5744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5744 eq16857
  have eq16952 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16946 eq16947
    | exact resolve eq16947 eq16946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16946 eq16947
  have eq16974 : (M.op x y) = (k (M.op x y) (τ (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16952 eq5776
    | exact resolve eq5776 eq16952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5776 eq16952
  have eq17023 : (M.op x y) = (k (M.op x y) (τ (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq16974
  have eq17057 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq17023
    | exact resolve eq17023 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17023
  have eq17077 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17057
       have r₂ := eq1713
       grind)
    | exact resolve eq17057 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713 eq17057
  have eq17192 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17077 eq1714
    | exact resolve eq1714 eq17077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq17196 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17077 eq42
    | exact resolve eq42 eq17077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq17077
  have eq17207 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17192
  have eq17212 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq17196
    | exact resolve eq17196 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17196
  have eq17214 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3863 eq17212
    | exact resolve eq17212 eq3863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863 eq17212
  have eq17224 : (k y x) = (τ (k (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17207 eq115
    | exact resolve eq115 eq17207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq17207
  have eq17334 : (k x x) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98 eq17224
    | exact resolve eq17224 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq17224
  have eq17350 : y = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17334
       have i₂ := eq1304
       grind)
    | exact superpose eq1304 eq17334
    | exact resolve eq17334 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq17334
  have eq17356 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1811 eq17350
    | exact resolve eq17350 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811 eq17350
  have eq17357 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17356
  have eq17359 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17357
       grind)
    | exact superpose eq17357 eq18
    | exact resolve eq18 eq17357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17517 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq17214 eq32
    | exact resolve eq32 eq17214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17214
  have eq17641 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30 eq17517
    | exact resolve eq17517 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17517
  have eq17658 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq17357 eq17641
    | exact resolve eq17641 eq17357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17357 eq17641
  have eq17659 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq17658
  have eq17693 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17659 eq3873
    | (have r₁ := eq3873
       have r₂ := eq17659
       grind)
    | exact resolve eq3873 eq17659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3873
  have eq17739 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq17693
  have eq17740 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq17739
  have eq17896 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17740 eq696
    | exact resolve eq696 eq17740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17939 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17740 eq17896
    | exact resolve eq17896 eq17740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17740 eq17896
  have eq18089 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17939 eq26
    | (have j1 := eq17939 (σ y)
       grind)
    | exact resolve eq26 eq17939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17939
  have eq18180 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18089 eq27
    | exact resolve eq27 eq18089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18089
  have eq18311 : y = (M.op x y) := by
    first
    | (have r₁ := eq18180
       have r₂ := eq17659
       grind)
    | exact resolve eq18180 eq17659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17659 eq18180
  have eq18330 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18311
       grind)
    | exact superpose eq18311 eq18
    | exact resolve eq18 eq18311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq18331 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq18311
       grind)
    | exact superpose eq18311 eq24
    | exact resolve eq24 eq18311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq18335 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq182
       have i₂ := eq18311
       grind)
    | exact superpose eq18311 eq182
    | exact resolve eq182 eq18311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq18342 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2407
       have i₂ := eq18311
       grind)
    | exact superpose eq18311 eq2407
    | exact resolve eq2407 eq18311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407
  have eq18350 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18331 eq20
    | exact resolve eq20 eq18331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18370 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq18331 eq338
    | exact resolve eq338 eq18331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq18776 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq18335 eq828
    | (have j0 := eq828 (σ (M.op (M.op x y) (M.op x y))) (σ y)
       grind)
    | (have r₁ := eq828 (σ (M.op (M.op x y) (M.op x y))) (σ y)
       have r₂ := eq18335
       grind)
    | exact resolve eq828 eq18335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18777 : (σ y) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) := by grind
  clear eq18776
  have eq21293 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq18342 eq804
    | (have j0 := eq804 (M.op x y) (M.op x y) x x
       grind)
    | exact resolve eq804 eq18342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq18342
  have eq21296 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq21293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21293
  have eq21301 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6779 eq21296
    | (have j1 := eq6779 y (M.op x y)
       grind)
    | exact resolve eq21296 eq6779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6779 eq21296
  have eq34122 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21301 eq18335
    | exact resolve eq18335 eq21301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18335
  have eq34123 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21301 eq18777
    | exact resolve eq18777 eq21301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21301
  have eq34194 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq34123
    | exact resolve eq34123 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34123
  have eq34195 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq34122
    | exact resolve eq34122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34122
  have eq34211 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18350 eq34194
    | exact resolve eq34194 eq18350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34194
  have eq34212 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18350 eq34195
    | exact resolve eq34195 eq18350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34195
  have eq34220 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq34211
    | exact resolve eq34211 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34211
  have eq34221 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34212
       have r₂ := eq1327
       grind)
    | exact resolve eq34212 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327 eq34212
  have eq34223 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18350 eq34220
    | exact resolve eq34220 eq18350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34220
  have eq34224 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34223
  have eq34225 : (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1302 eq34224
    | exact resolve eq34224 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302 eq34224
  have eq34226 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34225
  have eq34399 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34221 eq18370
    | exact resolve eq18370 eq34221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18370
  have eq34406 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34221 eq828
    | (have j0 := eq828 (σ y) (σ y)
       grind)
    | (have r₁ := eq828 (σ y) (σ y)
       have r₂ := eq34221
       grind)
    | exact resolve eq828 eq34221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34221
  have eq34407 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34406
  have eq34408 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34407
  have eq34427 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34226 eq34408
    | exact resolve eq34408 eq34226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34226 eq34408
  have eq34433 : y = (k y (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq34399
    | exact resolve eq34399 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34399
  have eq34442 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34433
       have i₂ := eq18311
       grind)
    | exact superpose eq18311 eq34433
    | exact resolve eq34433 eq18311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18311 eq34433
  have eq35422 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34427 eq1381
    | exact resolve eq1381 eq34427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381 eq34427
  have eq35498 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq35422
  have eq35529 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq35498
    | exact resolve eq35498 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35498
  have eq35705 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34442 eq828
    | (have j0 := eq828 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq828 (M.op x y) (M.op x y)
       have r₂ := eq34442
       grind)
    | exact resolve eq828 eq34442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34442
  have eq35706 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq35705
  have eq35707 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq35706
  have eq36908 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq828 x x
       have i₂ := eq35529
       grind)
    | exact superpose eq35529 eq828
    | (have j0 := eq828 x x
       grind)
    | (have r₁ := eq828 x x
       have r₂ := eq35529
       grind)
    | exact resolve eq828 eq35529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq35529
  have eq36909 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq36908
  have eq36910 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq36909
  have eq36945 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq35707 eq694
    | exact resolve eq694 eq35707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq36975 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq35707 eq696
    | exact resolve eq696 eq35707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq36986 : x ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq37003 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq35707 eq36975
    | exact resolve eq36975 eq35707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35707 eq36975
  have eq37016 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq36910 eq36945
    | exact resolve eq36945 eq36910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36910 eq36945
  have eq37040 : x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37003 eq37016
    | (have j0 := eq37016 (M.op x y)
       grind)
    | exact resolve eq37016 eq37003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37003 eq37016
  have eq37053 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq37040
       have r₂ := eq36986
       grind)
    | exact resolve eq37040 eq36986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36986 eq37040
  have eq37112 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq37053 eq1045
    | exact resolve eq1045 eq37053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq37053
  have eq37208 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq37112 X0 x
       have i₂ := eq3969 x
       grind)
    | exact superpose eq3969 eq37112
    | (have j1 := eq3969 x
       grind)
    | exact resolve eq37112 eq3969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3969
  have eq37310 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18330
       have i₂ := eq37112 sF0 x
       grind)
    | (have i₁ := eq18330
       have i₂ := eq37112 X0 sF0
       grind)
    | exact superpose eq37112 eq18330
    | (have j1 := eq37112 y X0
       grind)
    | exact resolve eq18330 eq37112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37311 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17359
       have i₂ := eq37112 sF0 x
       grind)
    | (have i₁ := eq17359
       have i₂ := eq37112 X0 sF0
       grind)
    | exact superpose eq37112 eq17359
    | (have j1 := eq37112 y X0
       grind)
    | exact resolve eq17359 eq37112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17359 eq37112
  have eq37397 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq37310 eq37208
    | (have j0 := eq37208 y
       grind)
    | exact resolve eq37208 eq37310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37208
  have eq37408 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37310 eq37397
    | exact resolve eq37397 eq37310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37310 eq37397
  have eq38726 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq37408
       grind)
    | exact superpose eq37408 eq40
    | exact resolve eq40 eq37408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq37408
  have eq38744 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38726
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38726
    | exact resolve eq38726 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38726
  have eq38746 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq38744
    | exact resolve eq38744 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38744
  have eq38748 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18350 eq38746
    | exact resolve eq38746 eq18350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38746
  have eq39082 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38748 eq6341
    | exact resolve eq6341 eq38748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6341 eq38748
  have eq39108 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39082
  have eq39137 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39108 eq27
    | exact resolve eq27 eq39108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39108
  have eq39190 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq39137
       have r₂ := eq18350
       grind)
    | exact resolve eq39137 eq18350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39137
  have eq39196 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39190 eq27
    | exact resolve eq27 eq39190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39225 : x = (M.op (τ (σ x)) x) ∨ (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39190 eq3715
    | exact resolve eq3715 eq39190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3715
  have eq39294 : x = (M.op x x) ∨ (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq39225
    | exact resolve eq39225 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39225
  have eq39304 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18350 eq39196
    | exact resolve eq39196 eq18350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39196
  have eq39305 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq39294
    | exact resolve eq39294 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39294
  have eq39306 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq39305
  have eq39309 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq39306
       have r₂ := eq39304
       grind)
    | exact resolve eq39306 eq39304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39306
  have eq40422 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37311 x
       have i₂ := eq39309
       grind)
    | exact superpose eq39309 eq37311
    | exact resolve eq37311 eq39309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37311 eq39309
  have eq40450 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40422
  have eq40470 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39190 eq40450
    | exact resolve eq40450 eq39190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39190 eq40450
  have eq40508 : x = (M.op x y) := by
    first
    | (have r₁ := eq40470
       have r₂ := eq39304
       grind)
    | exact resolve eq40470 eq39304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39304 eq40470
  have eq40525 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq40508
       grind)
    | exact superpose eq40508 eq22
    | exact resolve eq22 eq40508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq40591 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq18330
       have i₂ := eq40508
       grind)
    | exact superpose eq40508 eq18330
    | exact resolve eq18330 eq40508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18330 eq40508
  have eq40660 : (σ x) = (σ y) := by
    first
    | exact superpose eq40525 eq18331
    | exact resolve eq18331 eq40525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18331
  have eq40661 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq40525 eq20
    | exact resolve eq20 eq40525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40525
  have eq40832 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40660 eq26
    | exact resolve eq26 eq40660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq40925 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ x)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40660 eq18777
    | exact resolve eq18777 eq40660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18777
  have eq40975 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40591 eq40925
    | exact resolve eq40925 eq40591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40925
  have eq41009 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq40975
    | exact resolve eq40975 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40975
  have eq41028 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18350 eq41009
    | exact resolve eq41009 eq18350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18350 eq41009
  have eq41038 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40660 eq41028
    | exact resolve eq41028 eq40660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40660 eq41028
  have eq41044 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40832 eq41038
    | exact resolve eq41038 eq40832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41038
  have eq41046 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40832 eq41044
    | exact resolve eq41044 eq40832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40832 eq41044
  have eq41047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40591 eq41046
    | exact resolve eq41046 eq40591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40591 eq41046
  have eq41048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq41047
    | exact resolve eq41047 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq41047
  have eq41049 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41048
       have r₂ := eq27
       grind)
    | exact resolve eq41048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41048
  have eq41159 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq41049 eq27
    | exact resolve eq27 eq41049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq41049
  have eq41254 : False := by grind
  exact eq41254

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_pyy_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
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
  have eq48 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X2) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 (M.op X0 X1) x x X4
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq74 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq74
  have eq92 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq92
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq118 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq136 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq118 eq16
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq158 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq120
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq120 eq16
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq158
  have eq207 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq209 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq161
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq161
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq161 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq209
  have eq213 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq222 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X2) := by
    intro X2
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq426 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 x X1
       have i₂ := eq53 X0 x X2
       grind)
    | (have i₁ := eq53 X0 X0 x
       have i₂ := eq53 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq483 : (k x (k x x)) = (τ (k (σ x) (k (σ x) (σ x)))) := by
    first
    | exact superpose eq62 eq271
    | exact resolve eq271 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq1551 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ X0) X1) X2) X3) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (σ X0) X1 X2 X3
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq14
    | (have j1 := eq71 X0 X0
       grind)
    | exact resolve eq14 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1552 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq1567 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1568 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1567 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq1574 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1552 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1575 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ X0) X1) X2) X3) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1551 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1581 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1574 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq1574
    | (have j0 := eq1574 X0
       grind)
    | exact resolve eq1574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq5214 : (k x (k x x)) = (τ (k (σ x) (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq483
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq483
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq483 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq5244 : (k x (k x x)) = (τ (k (σ x) (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5214
  have eq5246 : (τ (σ x)) = (k x (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5244
  have eq5247 : x = (k x (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29 eq5246
    | exact resolve eq5246 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5246
  have eq6860 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1568 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1568
    | (have j0 := eq1568 (τ X0)
       grind)
    | exact resolve eq1568 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq6868 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6860 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6860
    | (have j0 := eq6860 X0
       grind)
    | exact resolve eq6860 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6860
  have eq6874 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6868 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6868
    | (have j0 := eq6868 X0
       grind)
    | exact resolve eq6868 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6868
  have eq12543 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq156 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq156
    | (have j0 := eq156 x
       grind)
    | exact resolve eq156 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq12571 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12543
  have eq12587 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12571
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq12571
    | exact resolve eq12571 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq12571
  have eq13697 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq207
    | (have j0 := eq207 (M.op x y)
       grind)
    | exact resolve eq207 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq13721 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq13697
  have eq13729 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq120 eq13721
    | exact resolve eq13721 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq13721
  have eq14260 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (σ X0) X1) X2) X3) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1575 X0 X1 X2 X3
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq1575
    | (have j0 := eq1575 X0 X1 X2 X3
       have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq1575 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq14394 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (σ X0) X1) X2) X3) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq14260 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14260
  have eq14621 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | exact superpose eq30 eq244
    | (have j0 := eq244 X0 x
       grind)
    | exact resolve eq244 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq14716 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | exact superpose eq37 eq14621
    | (have j0 := eq14621 X0
       grind)
    | exact resolve eq14621 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq14621
  have eq15149 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y (k X0 (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq95 (k X0 (k X0 X0))
       have i₂ := eq1581 X0
       grind)
    | exact superpose eq1581 eq95
    | (have j0 := eq95 X0
       have j1 := eq1581 X0
       grind)
    | exact resolve eq95 eq1581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq1581
  have eq15261 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y (k X0 (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15149
  have eq18176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18177 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18176
    | exact resolve eq18176 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18176
  have eq18188 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18177
       have r₂ := eq28
       grind)
    | exact resolve eq18177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18177
  have eq18194 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq18188
  have eq18248 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18194 eq104
    | exact resolve eq104 eq18194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq18194
  have eq18257 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18248
  have eq18277 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18257
  have eq18339 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18277 eq62
    | exact resolve eq62 eq18277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18277
  have eq18370 : x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq18339
    | exact resolve eq18339 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18339
  have eq18373 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq6874 x
       grind)
    | (have r₁ := eq18370
       have r₂ := eq6874 x
       grind)
    | exact resolve eq18370 eq6874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18370
  have eq18381 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq426 y X1 x
       have i₂ := eq18373
       grind)
    | exact superpose eq18373 eq426
    | exact resolve eq426 eq18373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18385 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y y x x
       have i₂ := eq18373
       grind)
    | exact superpose eq18373 eq14
    | exact resolve eq14 eq18373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18373
  have eq18582 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18381 y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18381
    | (have j0 := eq18381 y X0
       grind)
    | exact resolve eq18381 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18381
  have eq18692 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18582 x
       grind)
    | (have i₁ := eq78
       have i₂ := eq18582 x
       grind)
    | exact superpose eq18582 eq78
    | exact resolve eq78 eq18582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18733 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18582
  have eq18761 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq18692
    | exact resolve eq18692 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18692
  have eq18821 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18385 y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18385
    | (have j0 := eq18385 y X0
       grind)
    | exact resolve eq18385 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18385
  have eq18952 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18821 eq166
    | exact resolve eq166 eq18821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq18821
  have eq19010 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq18952
       have r₂ := eq18733
       grind)
    | exact resolve eq18952 eq18733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18952
  have eq19017 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19010
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19010
    | exact resolve eq19010 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19010
  have eq19020 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13729 eq19017
    | exact resolve eq19017 eq13729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13729
  have eq19024 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19017 eq161
    | exact resolve eq161 eq19017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19017
  have eq19047 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq19024
    | exact resolve eq19024 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19024
  have eq20013 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq18761
       have r₂ := eq18733
       grind)
    | exact resolve eq18761 eq18733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18761
  have eq20015 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12587 eq20013
    | exact resolve eq20013 eq12587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47007 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  have eq47058 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq20015
  have eq47259 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq47007 eq20013
    | exact resolve eq20013 eq47007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20013 eq47007
  have eq47305 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq47259
  have eq47318 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq47305
       have r₂ := eq47058
       grind)
    | exact resolve eq47305 eq47058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47058 eq47305
  have eq47668 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq47318 eq14
    | exact resolve eq14 eq47318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47318
  have eq48571 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq19020 eq47668
    | exact resolve eq47668 eq19020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19020 eq47668
  have eq48695 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq48571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48571
  have eq55952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq48695 eq27
    | (have j1 := eq48695 (σ y)
       grind)
    | exact resolve eq27 eq48695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48695
  have eq56056 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq55952
       have r₂ := eq28
       grind)
    | exact resolve eq55952 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55952
  have eq56112 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq56056
  have eq56233 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq56112 eq161
    | exact resolve eq161 eq56112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq56112
  have eq56309 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq31 eq56233
    | exact resolve eq56233 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56233
  have eq57434 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq56309 eq19047
    | exact resolve eq19047 eq56309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19047 eq56309
  have eq57481 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq57434
  have eq57509 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq57481
       have r₂ := eq18733
       grind)
    | exact resolve eq57481 eq18733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18733 eq57481
  have eq57544 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq213 X0
       have i₂ := eq57509
       grind)
    | exact superpose eq57509 eq213
    | exact resolve eq213 eq57509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57550 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  have eq57554 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq426 x X1 x
       have i₂ := eq57509
       grind)
    | exact superpose eq57509 eq426
    | exact resolve eq426 eq57509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57564 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq48 x x X2 X3 x x
       have i₂ := eq57509
       grind)
    | exact superpose eq57509 eq48
    | exact resolve eq48 eq57509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57509
  have eq57631 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ (σ (M.op x y)) = (σ y) := by
    intro X3
    first
    | (have i₁ := eq57564 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq57564
    | exact resolve eq57564 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57564
  have eq57654 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq57631 x
       have i₂ := eq213 x
       grind)
    | exact superpose eq213 eq57631
    | exact resolve eq57631 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq57631
  have eq57700 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1568 x
       have i₂ := eq57550
       grind)
    | exact superpose eq57550 eq1568
    | (have j0 := eq1568 x
       grind)
    | exact resolve eq1568 eq57550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57550
  have eq57727 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq57700
  have eq57760 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq57727
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57727
    | exact resolve eq57727 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57727
  have eq57815 : (M.op x y) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by grind
  have eq57951 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq57760 eq222
    | exact resolve eq222 eq57760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57958 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq57760 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq57760
       grind)
    | exact resolve eq12 eq57760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57973 : ∀ X0 X1 X2 X3 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) X0) X1) X2) X3) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq57760 eq48
    | exact resolve eq48 eq57760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57760
  have eq58012 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq57958 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57958
  have eq58041 : ∀ X3 : G, (σ x) = (M.op (M.op (σ x) (σ x)) X3) ∨ (σ (M.op x y)) = (σ y) := by
    intro X3
    first
    | (have i₁ := eq57973 x x X3 X3
       have i₂ := eq14 sF2 x x X3
       grind)
    | exact superpose eq14 eq57973
    | exact resolve eq57973 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57973
  have eq58064 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq222 eq58041
    | exact resolve eq58041 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58041
  have eq58168 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq57815 eq118
    | exact resolve eq118 eq57815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq57815
  have eq58231 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq58168
    | exact resolve eq58168 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58168
  have eq58465 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq57544 eq57654
    | exact resolve eq57654 eq57544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57654
  have eq58651 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq58465 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58465
  have eq58892 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58651 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58651
    | (have j0 := eq58651 y
       grind)
    | exact resolve eq58651 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58651
  have eq59105 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58892 eq30
    | exact resolve eq30 eq58892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58892
  have eq59235 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq59105
    | exact resolve eq59105 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59105
  have eq59393 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq59235
  have eq59627 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq57554 y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57554
    | (have j0 := eq57554 y X0
       grind)
    | exact resolve eq57554 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57554
  have eq59996 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq57544 x
       have i₂ := eq59627 x
       grind)
    | (have i₁ := eq57544 y
       have i₂ := eq59627 x
       grind)
    | exact superpose eq59627 eq57544
    | (have j0 := eq57544 y
       grind)
    | exact resolve eq57544 eq59627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57544 eq59627
  have eq60062 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59996
  have eq60335 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq60062
  have eq60591 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq60335 eq1568
    | (have j0 := eq1568 (M.op x y)
       grind)
    | exact resolve eq1568 eq60335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60335
  have eq60618 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq60591
  have eq60654 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq60618
    | exact resolve eq60618 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60618
  have eq63318 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq57951 eq58064
    | exact resolve eq58064 eq57951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57951 eq58064
  have eq63431 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq63318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63318
  have eq63669 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq63431
    | (have j0 := eq63431 (σ y)
       grind)
    | exact resolve eq63431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63431
  have eq64159 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq63669 eq28
    | exact resolve eq28 eq63669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63669
  have eq165392 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq58012 eq58231
    | (have j1 := eq58012 (σ (M.op x y))
       grind)
    | exact resolve eq58231 eq58012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58012 eq58231
  have eq165471 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq165392
  have eq165538 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq165471
       have r₂ := eq64159
       grind)
    | exact resolve eq165471 eq64159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165471
  have eq165620 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq165538 eq60654
    | exact resolve eq60654 eq165538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60654 eq165538
  have eq165720 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq165620
  have eq165763 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq165720
       have r₂ := eq64159
       grind)
    | exact resolve eq165720 eq64159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64159 eq165720
  have eq165789 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq165763 eq27
    | exact resolve eq27 eq165763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165790 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq165763 eq30
    | exact resolve eq30 eq165763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq165958 : y = (M.op x y) := by
    first
    | exact superpose eq31 eq165790
    | exact resolve eq165790 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165790
  have eq167700 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq14716 x
       grind)
    | exact superpose eq14716 eq92
    | (have j1 := eq14716 x
       grind)
    | exact resolve eq92 eq14716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14716
  have eq167980 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq165763 eq167700
    | exact resolve eq167700 eq165763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167700
  have eq168099 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq167980
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq167980
    | exact resolve eq167980 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167980
  have eq168146 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq168099
    | exact resolve eq168099 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168099
  have eq254958 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq168146 eq136
    | exact resolve eq136 eq168146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq254975 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq168146 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq168146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168146
  have eq254992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq165789 eq254975
    | exact resolve eq254975 eq165789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254975
  have eq255000 : (τ (σ (M.op x y))) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq165958 eq254958
    | exact resolve eq254958 eq165958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254958
  have eq255004 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq254992
       have r₂ := eq28
       grind)
    | exact resolve eq254992 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254992
  have eq255011 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq255000
    | exact resolve eq255000 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255000
  have eq255020 : y = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq165958 eq255011
    | exact resolve eq255011 eq165958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255011
  have eq295691 : ∀ X0 X1 X2 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (M.op (σ (M.op x y)) X0) X1) X2) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq21 eq14394
    | (have j0 := eq14394 (M.op x y) X0 X1 X2
       grind)
    | exact resolve eq14394 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq14394
  have eq296460 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq295691 x x x
       have i₂ := eq14 sF1 x x x
       grind)
    | exact superpose eq14 eq295691
    | exact resolve eq295691 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295691
  have eq296752 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq165958 eq296460
    | exact resolve eq296460 eq165958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296460
  have eq296982 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq165958 eq296752
    | exact resolve eq296752 eq165958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296752
  have eq325633 : ∀ X0 : G, (M.op (σ X0) (σ (M.op x y))) = (σ (k y (k X0 (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq165763 eq15261
    | (have j0 := eq15261 X0
       grind)
    | exact resolve eq15261 eq165763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15261
  have eq325634 : ∀ X0 : G, (M.op (σ X0) (σ (M.op x y))) = (σ (k y (k X0 (k X0 X0)))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq165763 eq325633
    | (have j0 := eq325633 X0
       grind)
    | exact resolve eq325633 eq165763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325633
  have eq325703 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq325634 x
       have i₂ := eq5247
       grind)
    | exact superpose eq5247 eq325634
    | (have j0 := eq325634 x
       grind)
    | exact resolve eq325634 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5247 eq325634
  have eq326008 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq325703
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq325703
    | exact resolve eq325703 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325703
  have eq326073 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq165789 eq326008
    | exact resolve eq326008 eq165789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326008
  have eq326117 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq326073
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq326073
    | exact resolve eq326073 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326073
  have eq326157 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq165763 eq326117
    | exact resolve eq326117 eq165763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326117
  have eq326196 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq326157
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq326157
    | exact resolve eq326157 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326157
  have eq326223 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq326196
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq326196
    | exact resolve eq326196 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326196
  have eq326224 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq326223
  have eq465542 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq296982
       grind)
    | exact superpose eq296982 eq16
    | exact resolve eq16 eq296982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296982
  have eq1084196 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq255004
  have eq1112412 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1084196 eq62
    | exact resolve eq62 eq1084196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1084196
  have eq1112784 : x = (k x x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1112412
    | exact resolve eq1112412 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112412
  have eq1112812 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq6874 x
       grind)
    | (have r₁ := eq1112784
       have r₂ := eq6874 x
       grind)
    | exact resolve eq1112784 eq6874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112784
  have eq1112823 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1112812 eq211
    | exact resolve eq211 eq1112812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq1112855 : (τ (σ x)) = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1112812 eq465542
    | exact resolve eq465542 eq1112812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465542 eq1112812
  have eq1113046 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1112855
    | exact resolve eq1112855 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112855
  have eq1113047 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by grind
  clear eq1113046
  have eq1113059 : (τ (σ x)) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq165958 eq1112823
    | exact resolve eq1112823 eq165958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112823
  have eq1113079 : x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1113059
    | exact resolve eq1113059 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113059
  have eq1120730 : y = (k y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by grind
  have eq1120795 : x ≠ y ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by grind
  clear eq1113047
  have eq1122493 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1113079
       have i₂ := eq1120730
       grind)
    | exact superpose eq1120730 eq1113079
    | exact resolve eq1113079 eq1120730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113079 eq1120730
  have eq1122759 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq1122493
  have eq1122959 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1122759
       have r₂ := eq1120795
       grind)
    | exact resolve eq1122759 eq1120795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120795 eq1122759
  have eq1123921 : y = (k y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  have eq1123925 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq426 y X1 x
       have i₂ := eq1122959
       grind)
    | exact superpose eq1122959 eq426
    | exact resolve eq426 eq1122959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122959
  have eq1124169 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq1123921
       grind)
    | exact superpose eq1123921 eq92
    | exact resolve eq92 eq1123921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1123921
  have eq1124361 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq165763 eq1124169
    | exact resolve eq1124169 eq165763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124169
  have eq1124450 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1124361
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1124361
    | exact resolve eq1124361 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124361
  have eq1124535 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq165763 eq1124450
    | exact resolve eq1124450 eq165763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124450
  have eq1124809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1124535 eq326224
    | exact resolve eq326224 eq1124535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326224 eq1124535
  have eq1124892 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1124809
       have r₂ := eq28
       grind)
    | exact resolve eq1124809 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124809
  have eq1125229 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq19
       have i₂ := eq1123925 y X0
       grind)
    | (have i₁ := eq19
       have i₂ := eq1123925 X0 y
       grind)
    | exact superpose eq1123925 eq19
    | (have j1 := eq1123925 y X0
       grind)
    | exact resolve eq19 eq1123925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1125340 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    grind
  clear eq1123925
  have eq1125500 : ∀ X0 : G, y = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq165958 eq1125229
    | exact resolve eq1125229 eq165958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125229
  have eq1125574 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1125340 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1125340
    | (have j0 := eq1125340 y
       grind)
    | exact resolve eq1125340 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125340
  have eq1125598 : x ≠ y ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq165958 eq1125574
    | exact resolve eq1125574 eq165958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125574
  have eq1125662 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq78
       have i₂ := eq1125500 x
       grind)
    | exact superpose eq1125500 eq78
    | exact resolve eq78 eq1125500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1125500
  have eq1125973 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1125662
       have r₂ := eq1125598
       grind)
    | exact resolve eq1125662 eq1125598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125598 eq1125662
  have eq1126037 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1125973
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1125973
    | exact resolve eq1125973 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125973
  have eq1126077 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq165763 eq1126037
    | exact resolve eq1126037 eq165763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126037
  have eq1128726 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12587 eq1126077
    | exact resolve eq1126077 eq12587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12587
  have eq1260682 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1124892
  have eq1272603 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1260682 eq1126077
    | exact resolve eq1126077 eq1260682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260682
  have eq1272878 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1272603
  have eq1273103 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq1272878 eq426
    | exact resolve eq426 eq1272878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272878
  have eq1276418 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq27 eq1273103
    | (have j0 := eq1273103 (σ y) X0
       grind)
    | exact resolve eq1273103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273103
  have eq1276959 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1276418 eq1128726
    | exact resolve eq1128726 eq1276418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128726 eq1276418
  have eq1277075 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq1276959
  have eq1277163 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1277075
       have r₂ := eq28
       grind)
    | exact resolve eq1277075 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277075
  have eq1277268 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1277163
  have eq1279932 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1568 x
       have i₂ := eq1277268
       grind)
    | exact superpose eq1277268 eq1568
    | (have j0 := eq1568 x
       grind)
    | exact resolve eq1568 eq1277268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277268
  have eq1280175 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1279932
  have eq1280358 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1280175
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1280175
    | exact resolve eq1280175 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280175
  have eq1281286 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1280358 eq222
    | exact resolve eq222 eq1280358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1281336 : ∀ X0 X1 X2 X3 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) X0) X1) X2) X3) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1280358 eq48
    | exact resolve eq48 eq1280358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1280358
  have eq1281428 : ∀ X3 : G, (σ x) = (M.op (M.op (σ x) (σ x)) X3) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X3
    first
    | (have i₁ := eq1281336 x x X3 X3
       have i₂ := eq14 sF2 x x X3
       grind)
    | exact superpose eq14 eq1281336
    | exact resolve eq1281336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281336
  have eq1281453 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq222 eq1281428
    | exact resolve eq1281428 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq1281428
  have eq1322046 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1281286 eq1281453
    | exact resolve eq1281453 eq1281286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281286 eq1281453
  have eq1322285 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq1322046 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322046
  have eq1322631 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1322285 eq27
    | (have j1 := eq1322285 (σ y)
       grind)
    | exact resolve eq27 eq1322285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322285
  have eq1322741 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1322631
  have eq1325280 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq1322741 eq52
    | exact resolve eq52 eq1322741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1327579 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq27 eq1325280
    | (have j0 := eq1325280 (σ y) X0
       grind)
    | exact resolve eq1325280 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325280
  have eq1328149 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1322741 eq1327579
    | exact resolve eq1327579 eq1322741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327579
  have eq1328346 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq1328149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328149
  have eq1333511 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq1328346
    | (have j0 := eq1328346 (σ y)
       grind)
    | exact resolve eq1328346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1328346
  have eq1333959 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1333511
  have eq1334169 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1322741 eq1333959
    | exact resolve eq1333959 eq1322741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322741 eq1333959
  have eq1334228 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1334169
  have eq1340194 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1334228 eq1126077
    | exact resolve eq1126077 eq1334228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126077 eq1334228
  have eq1340471 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1340194
  have eq1340969 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq426 x X1 x
       have i₂ := eq1340471
       grind)
    | exact superpose eq1340471 eq426
    | exact resolve eq426 eq1340471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq1364807 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1340471
       have i₂ := eq1340969 x X0
       grind)
    | (have i₁ := eq1340471
       have i₂ := eq1340969 X0 x
       grind)
    | exact superpose eq1340969 eq1340471
    | exact resolve eq1340471 eq1340969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340471 eq1340969
  have eq1364924 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq1364807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364807
  have eq1365249 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1364924 y
       grind)
    | exact superpose eq1364924 eq19
    | (have j1 := eq1364924 y
       grind)
    | exact resolve eq19 eq1364924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1364924
  have eq1365460 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq165958 eq1365249
    | exact resolve eq1365249 eq165958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365249
  have eq1365559 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1365460 eq29
    | exact resolve eq29 eq1365460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1365460
  have eq1365980 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1365559
    | exact resolve eq1365559 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1365559
  have eq1366054 : x = (M.op x y) := by
    first
    | (have r₁ := eq1365980
       have r₂ := eq59393
       grind)
    | exact resolve eq1365980 eq59393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59393 eq1365980
  have eq1366058 : x = y := by
    first
    | exact superpose eq165958 eq1366054
    | exact resolve eq1366054 eq165958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165958 eq1366054
  have eq1366060 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1366058
       grind)
    | exact superpose eq1366058 eq25
    | exact resolve eq25 eq1366058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1366320 : x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq255020
       have i₂ := eq1366058
       grind)
    | exact superpose eq1366058 eq255020
    | exact resolve eq255020 eq1366058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255020 eq1366058
  have eq1366548 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq1366320
  have eq1366559 : x = (M.op x x) := by
    first
    | (have j1 := eq6874 x
       grind)
    | (have r₁ := eq1366548
       have r₂ := eq6874 x
       grind)
    | exact resolve eq1366548 eq6874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6874 eq1366548
  have eq1366728 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq165763 eq1366060
    | exact resolve eq1366060 eq165763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165763 eq1366060
  have eq1366874 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1366728
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1366728
    | exact resolve eq1366728 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366728
  have eq1367142 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1366874 eq165789
    | exact resolve eq165789 eq1366874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165789
  have eq1367520 : x = (k x x) := by grind
  clear eq1366559
  have eq1383582 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1568 x
       have i₂ := eq1367520
       grind)
    | exact superpose eq1367520 eq1568
    | (have j0 := eq1568 x
       grind)
    | exact resolve eq1568 eq1367520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568 eq1367520
  have eq1383837 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1383582
  have eq1384012 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1383837
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1383837
    | exact resolve eq1383837 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1383837
  have eq1384244 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1366874 eq1384012
    | exact resolve eq1384012 eq1366874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366874 eq1384012
  have eq1384472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1367142 eq1384244
    | exact resolve eq1384244 eq1367142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367142 eq1384244
  have eq1384698 : False := by grind
  exact eq1384698

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation4079 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  have eq57 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 (M.op X0 X1) x x X4
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  clear eq49
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq128 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq125
  have eq129 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq128
  have eq168 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X2) := by
    intro X2
    first
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq257 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq246 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq246
    | exact resolve eq246 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq258 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq257
  have eq573 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq74 eq258
    | exact resolve eq258 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq600 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | exact superpose eq226 eq573
    | exact resolve eq573 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq573
  have eq602 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq600
       have i₂ := eq218 (M.op x x)
       grind)
    | exact superpose eq218 eq600
    | exact resolve eq600 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq603 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq129 eq602
    | exact resolve eq602 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq644 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 x X1
       have i₂ := eq59 X0 x X2
       grind)
    | (have i₁ := eq59 X0 X0 x
       have i₂ := eq59 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1125 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq644 (σ X0) X1 X2
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq644
    | exact resolve eq644 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq644
  have eq1205 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1205
    | exact resolve eq1205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1209 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1206
       have r₂ := eq28
       grind)
    | exact resolve eq1206 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1211 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1209
    | exact resolve eq1209 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1213 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1211 eq603
    | exact resolve eq603 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq1215 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1211 eq58
    | exact resolve eq58 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq799749 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq1215
    | (have j0 := eq1215 (σ y) X0
       grind)
    | exact resolve eq1215 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800423 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1211 eq799749
    | exact resolve eq799749 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799749
  have eq800554 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq800423 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800423
  have eq800793 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq800554
    | (have j0 := eq800554 (σ y)
       grind)
    | exact resolve eq800554 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800554
  have eq801126 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq800793 eq1215
    | exact resolve eq1215 eq800793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215 eq800793
  have eq801234 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq801126 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801126
  have eq801417 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1211 eq801234
    | exact resolve eq801234 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211 eq801234
  have eq801541 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq801417 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801417
  have eq802388 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq801541 eq74
    | exact resolve eq74 eq801541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802390 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq801541 eq1213
    | exact resolve eq1213 eq801541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq801541
  have eq802523 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq802390
  have eq802591 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq802388
    | exact resolve eq802388 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802388
  have eq802665 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq802523 eq168
    | exact resolve eq168 eq802523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq802523
  have eq802838 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq802665
    | exact resolve eq802665 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802665
  have eq802897 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq802591
       grind)
    | exact superpose eq802591 eq218
    | exact resolve eq218 eq802591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq802591
  have eq831362 : ∀ X0 : G, x = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq802897 eq802838
    | exact resolve eq802838 eq802897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802838 eq802897
  have eq831477 : ∀ X0 : G, x = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq831362 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831362
  have eq831962 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19
       have i₂ := eq831477 y
       grind)
    | exact superpose eq831477 eq19
    | (have j1 := eq831477 y
       grind)
    | exact resolve eq19 eq831477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831477
  have eq832076 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq831962
  have eq832333 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq832076 eq30
    | exact resolve eq30 eq832076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq832076
  have eq833959 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq832333
    | exact resolve eq832333 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq832333
  have eq833960 : x = (M.op x y) ∨ x = y := by grind
  clear eq833959
  have eq833988 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq833960 eq21
    | exact resolve eq21 eq833960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833990 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x X0) X1) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq833960 eq57
    | exact resolve eq57 eq833960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq834401 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq833988
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq833988
    | exact resolve eq833988 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833988
  have eq834435 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq834401 eq27
    | exact resolve eq27 eq834401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834401
  have eq850761 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq833990 y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq833990
    | (have j0 := eq833990 y X0
       grind)
    | exact resolve eq833990 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851610 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq833960 eq850761
    | exact resolve eq850761 eq833960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833960 eq850761
  have eq851836 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq851610 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851610
  have eq853760 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq851836 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq851836
    | (have j0 := eq851836 y
       grind)
    | exact resolve eq851836 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851836
  have eq854196 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq833990 x x
       have i₂ := eq853760
       grind)
    | exact superpose eq853760 eq833990
    | exact resolve eq833990 eq853760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833990
  have eq854204 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1125 x X1 x
       have i₂ := eq853760
       grind)
    | exact superpose eq853760 eq1125
    | exact resolve eq1125 eq853760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq853760
  have eq854304 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq854196 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854196
  have eq854404 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq21 eq854204
    | (have j0 := eq854204 X0 X1
       grind)
    | exact resolve eq854204 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854204
  have eq854590 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq854304 eq129
    | exact resolve eq129 eq854304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq854304
  have eq854911 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq21 eq854590
    | exact resolve eq854590 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854590
  have eq864449 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq854404 eq834435
    | exact resolve eq834435 eq854404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834435 eq854404
  have eq864574 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq864449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864449
  have eq864712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq864574 eq854911
    | exact resolve eq854911 eq864574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854911 eq864574
  have eq864839 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq864712
  have eq864958 : x = y := by
    first
    | (have r₁ := eq864839
       have r₂ := eq28
       grind)
    | exact resolve eq864839 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864839
  have eq866261 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq864958
       grind)
    | exact superpose eq864958 eq19
    | exact resolve eq19 eq864958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq866262 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq864958
       grind)
    | exact superpose eq864958 eq25
    | exact resolve eq25 eq864958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq864958
  have eq866620 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq866262
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq866262
    | exact resolve eq866262 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq866262
  have eq866654 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq866620 eq27
    | exact resolve eq27 eq866620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq866620
  have eq867922 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq866654 eq74
    | exact resolve eq74 eq866654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq866654
  have eq868145 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq867922
       have i₂ := eq866261
       grind)
    | exact superpose eq866261 eq867922
    | exact resolve eq867922 eq866261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866261 eq867922
  have eq868263 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq868145 eq15
    | exact resolve eq15 eq868145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868145
  have eq868845 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq868263
    | exact resolve eq868263 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq868263
  have eq868998 : False := by grind
  exact eq868998

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq111 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq111 y x
       grind)
    | exact superpose eq111 eq98
    | (have j1 := eq111 y x
       grind)
    | exact resolve eq98 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq137 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126
    | exact resolve eq126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq139 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq137
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq140 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq139
    | exact resolve eq139 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq140 eq111
    | (have j0 := eq111 (σ y) (σ x)
       grind)
    | exact resolve eq111 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq145
    | exact resolve eq145 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq149 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq146
       have r₂ := eq27
       grind)
    | exact resolve eq146 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq151 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq149
    | exact resolve eq149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq273 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq151 eq55
    | exact resolve eq55 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq295 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq273
    | (have j0 := eq273 X0 X1
       grind)
    | exact resolve eq273 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq306 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq151 eq295
    | exact resolve eq295 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq394 : ∀ X0 X2 : G, (M.op (σ x) X0) = (M.op (σ x) X2) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq330 x X2
       have i₂ := eq330 x X0
       grind)
    | (have i₁ := eq330 (σ x) x
       have i₂ := eq330 X0 (σ x)
       grind)
    | exact superpose eq330 eq330
    | exact resolve eq330 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq330
    | (have j0 := eq330 X0 (σ y)
       grind)
    | exact resolve eq330 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq435 : ∀ X0 X2 : G, (M.op (σ x) X0) = (M.op (σ x) X2) ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | (have j0 := eq394 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq459 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq295 x X1
       have i₂ := eq401 x
       grind)
    | exact superpose eq401 eq295
    | exact resolve eq295 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq401
  have eq472 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq459 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq518 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq151 eq472
    | exact resolve eq472 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq472
  have eq542 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq518 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq1124 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X1) = (k X1 (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq435 eq13
    | (have j0 := eq13 X1 (σ x)
       grind)
    | exact resolve eq13 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq1168 : ∀ X1 : G, (M.op (σ x) X1) = (k X1 (σ x)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq1124 x X1
       grind)
    | (have r₁ := eq1124 x X1
       have r₂ := eq542 x
       grind)
    | exact resolve eq1124 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq1124
  have eq1841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1168 eq140
    | exact resolve eq140 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq1168
  have eq1844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1841
  have eq1847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1844
    | exact resolve eq1844 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq1849 : x = (M.op x y) := by
    first
    | (have r₁ := eq1847
       have r₂ := eq27
       grind)
    | exact resolve eq1847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq1852 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1849 eq20
    | exact resolve eq20 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1854 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq1849 eq54
    | exact resolve eq54 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1865 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1854 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1854
    | (have j0 := eq1854 X0 X1
       grind)
    | exact resolve eq1854 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1854
  have eq1867 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1852
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1852
    | exact resolve eq1852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852
  have eq1868 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x X1) := by
    intro X0 X1
    first
    | exact superpose eq1849 eq1865
    | exact resolve eq1865 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq1869 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1867 eq26
    | exact resolve eq26 eq1867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2005 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq1868 X0 y
       grind)
    | exact superpose eq1868 eq18
    | (have j1 := eq1868 X0 y
       grind)
    | exact resolve eq18 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2023 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq1849 eq2005
    | exact resolve eq2005 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849 eq2005
  have eq2043 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2023 x
       have i₂ := eq1868 x X0
       grind)
    | (have i₁ := eq2023 x
       have i₂ := eq1868 X0 x
       grind)
    | exact superpose eq1868 eq2023
    | exact resolve eq2023 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868 eq2023
  have eq2150 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq2043 x
       grind)
    | exact superpose eq2043 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq2043 x
       grind)
    | exact resolve eq13 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2168 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2150 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150
  have eq2176 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq2168 X0
       have i₂ := eq2043 X0
       grind)
    | exact superpose eq2043 eq2168
    | exact resolve eq2168 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043 eq2168
  have eq2192 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq2176 (τ X0)
       grind)
    | exact superpose eq2176 eq34
    | exact resolve eq34 eq2176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq2176
  have eq2197 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2192 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2192
    | (have j0 := eq2192 X0
       grind)
    | exact resolve eq2192 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2192
  have eq2201 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1867 eq2197
    | exact resolve eq2197 eq1867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867 eq2197
  have eq2214 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2201 eq111
    | (have j0 := eq111 X0 (σ (M.op x y))
       grind)
    | exact resolve eq111 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq2201
  have eq2216 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq2214 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq2313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2216 eq1869
    | exact resolve eq1869 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869 eq2216
  have eq2347 : False := by grind
  exact eq2347

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_pxy_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
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
  have eq176 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X2) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq16 X3 X4 X4 X5
       have i₂ := eq16 X4 X0 X1 X2
       grind)
    | (have i₁ := eq16 X0 (M.op (M.op X1 X2) X2) X3 X3
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) y) X1) := by
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
  have eq179 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X1 (M.op x x) x X4
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | (have i₁ := eq16 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq16 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) ≠ X1 ∨ (k X2 X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq179 X0 X1
       grind)
    | (have i₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have i₂ := eq179 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq179 eq13
    | (have r₁ := eq13 X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1)
       have r₂ := eq179 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) X1
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq180 X3 x X4
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq180 X0 (M.op X0 X0) X4
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq180 x X1 X3
       have i₂ := eq179 x X0
       grind)
    | (have i₁ := eq180 (M.op (M.op (σ x) (σ y)) (σ y)) X1 x
       have i₂ := eq179 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq179 eq180
    | exact resolve eq180 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 X3) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq180 x X3 X5
       have i₂ := eq16 x X0 X1 X2
       grind)
    | (have i₁ := eq180 (M.op (M.op X1 X2) X2) X1 x
       have i₂ := eq16 X0 X1 X2 (M.op (M.op X1 X2) X2)
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) ≠ X2 ∨ (M.op (M.op X0 X0) X1) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq180 X0 X1 x
       grind)
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq180 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq180 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq179 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq1292 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 (M.op X0 X0) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1321 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq474 X1 (M.op X0 X0)
       have i₂ := eq1292 X0 (σ X1)
       grind)
    | exact superpose eq1292 eq474
    | exact resolve eq474 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (M.op X0 X0)
       have i₂ := eq1292 X0 (τ X1)
       grind)
    | exact superpose eq1292 eq34
    | exact resolve eq34 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1327 : ∀ X0 : G, (τ (M.op X0 X0)) = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op X0 X0)
       have i₂ := eq1292 X0 sF2
       grind)
    | exact superpose eq1292 eq90
    | exact resolve eq90 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1292
  have eq1426 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (k X1 X1) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = X1 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq179 X0 X1
       grind)
    | (have i₁ := eq11 X1 (M.op (M.op (σ x) (σ y)) (σ y))
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq11
    | exact resolve eq11 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1427 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k X2 X2) ∨ (M.op (M.op X0 X0) X1) = X2 ∨ (M.op (M.op X0 X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq180 X0 X1 x
       grind)
    | (have i₁ := eq11 x (M.op X0 X0)
       have i₂ := eq180 X0 X1 x
       grind)
    | exact superpose eq180 eq11
    | exact resolve eq11 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1429 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq11
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1451 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq1452 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1534 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1429 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1536 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k X2 X2) ∨ (M.op (M.op X0 X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1427 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1537 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (k X1 X1) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1426 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1564 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1534 X0 X1
       have j1 := eq197 X0 X1 X1
       grind)
    | (have r₁ := eq1534 X0 X1
       have r₂ := eq197 X0 (k X1 X1) x
       grind)
    | (have r₁ := eq1534 X0 X1
       have r₂ := eq197 X0 X1 x
       grind)
    | (have r₁ := eq1534 X0 (M.op X0 X0)
       have r₂ := eq197 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq1534 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq1534
  have eq1566 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1536 X0 X1 X2
       have j1 := eq276 X0 X1 X2 X2
       grind)
    | (have r₁ := eq1536 X0 X1 X2
       have r₂ := eq276 X0 X1 (k X2 X2) x
       grind)
    | (have r₁ := eq1536 X0 X1 X2
       have r₂ := eq276 X0 X1 X2 x
       grind)
    | (have r₁ := eq1536 X0 X1 (M.op (M.op X0 X0) X1)
       have r₂ := eq276 X0 X1 (M.op (M.op X0 X0) X1) x
       grind)
    | exact resolve eq1536 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq1536
  have eq1567 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1537 X0 X1
       have j1 := eq238 X0 X1 X1
       grind)
    | (have r₁ := eq1537 X0 X1
       have r₂ := eq238 X0 (k X1 X1) x
       grind)
    | (have r₁ := eq1537 X0 X1
       have r₂ := eq238 X0 X1 x
       grind)
    | (have r₁ := eq1537 X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)
       have r₂ := eq238 X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) x
       grind)
    | exact resolve eq1537 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq1537
  have eq1660 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) ∨ (k X0 X0) = X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq1564 X0 X1
       grind)
    | exact superpose eq1564 eq11
    | exact resolve eq11 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1679 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq260 (M.op sF4 sF3) X1 x
       have i₂ := eq1564 (M.op sF4 sF3) X1
       grind)
    | exact superpose eq1564 eq260
    | exact resolve eq260 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1686 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1322 X1 (σ (M.op X1 X1))
       have i₂ := eq1564 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq1564 eq1322
    | exact resolve eq1322 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1688 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X1 (τ (M.op X1 X1))
       have i₂ := eq1564 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1564 eq1321
    | exact resolve eq1321 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1690 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq474 X1 (σ X1)
       have i₂ := eq1564 X0 (σ X1)
       grind)
    | exact superpose eq1564 eq474
    | exact resolve eq474 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq1692 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1564 X0 (τ X1)
       grind)
    | exact superpose eq1564 eq34
    | exact resolve eq34 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1693 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1660 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1695 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1692 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq1692
    | exact resolve eq1692 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq1696 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1690 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq1690
    | exact resolve eq1690 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq2016 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X1 (τ (M.op X1 X1))
       have i₂ := eq1695 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1695 eq1321
    | exact resolve eq1321 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq2076 : ∀ X0 X1 X3 : G, (τ (M.op (M.op X0 X0) X1)) = (k X3 X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1696 (M.op x x) X3
       have i₂ := eq249 x (M.op x x) X0 X1
       grind)
    | (have i₁ := eq1696 (M.op x x) X3
       have i₂ := eq249 X0 X1 x (M.op x x)
       grind)
    | exact superpose eq249 eq1696
    | exact resolve eq1696 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2106 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X0 (τ (M.op X0 X0))
       have i₂ := eq1696 X1 (τ (M.op X0 X0))
       grind)
    | exact superpose eq1696 eq1321
    | exact resolve eq1321 eq1696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321 eq1696
  have eq2882 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq279 X0 X1 (M.op sF4 sF3)
       have i₂ := eq1686 (M.op sF4 sF3) X1
       grind)
    | exact superpose eq1686 eq279
    | exact resolve eq279 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2883 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq260 (M.op sF4 sF3) X1 x
       have i₂ := eq1686 (M.op sF4 sF3) X1
       grind)
    | exact superpose eq1686 eq260
    | exact resolve eq260 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq1686
  have eq3044 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq279 X0 X1 (M.op sF4 sF3)
       have i₂ := eq1688 (M.op sF4 sF3) X1
       grind)
    | exact superpose eq1688 eq279
    | exact resolve eq279 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq3099 : ∀ X0 X2 X3 : G, (k X3 X3) = (M.op (k X0 X0) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1566 (M.op x x) X2 X3
       have i₂ := eq1566 x (M.op x x) X0
       grind)
    | exact superpose eq1566 eq1566
    | exact resolve eq1566 eq1566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq5366 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X0) X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2016 X2 (M.op x x)
       have i₂ := eq249 x (M.op x x) X0 X1
       grind)
    | (have i₁ := eq2016 X2 (M.op x x)
       have i₂ := eq249 X0 X1 x (M.op x x)
       grind)
    | exact superpose eq249 eq2016
    | exact resolve eq2016 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016
  have eq5776 : ∀ X0 X1 X2 : G, (τ (M.op X2 X2)) = (τ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2106 X2 (M.op x x)
       have i₂ := eq249 x (M.op x x) X0 X1
       grind)
    | (have i₁ := eq2106 X2 (M.op x x)
       have i₂ := eq249 X0 X1 x (M.op x x)
       grind)
    | exact superpose eq249 eq2106
    | exact resolve eq2106 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq2106
  have eq7949 : ∀ X0 X1 X2 X4 : G, (M.op X2 X2) = (M.op (τ (M.op (M.op X0 X0) X1)) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1679 x X2 X4
       have i₂ := eq2076 X0 X1 x
       grind)
    | exact superpose eq2076 eq1679
    | exact resolve eq1679 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679 eq2076
  have eq11088 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1451
       grind)
    | exact superpose eq1451 eq39
    | exact resolve eq39 eq1451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1451
  have eq11089 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11088
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11088
    | exact resolve eq11088 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11088
  have eq11091 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq11089
    | exact resolve eq11089 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11089
  have eq13124 : ∀ X0 X2 X3 : G, (σ (M.op X3 X3)) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2882 X3 (M.op x x) X2
       have i₂ := eq2882 X0 x (M.op x x)
       grind)
    | exact superpose eq2882 eq2882
    | exact resolve eq2882 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882
  have eq13603 : ∀ X0 X1 X3 : G, (τ (M.op X3 X3)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1688 x X3
       have i₂ := eq2883 X0 x X1
       grind)
    | (have i₁ := eq1688 (σ (M.op X0 X0)) X1
       have i₂ := eq2883 X0 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq2883 eq1688
    | exact resolve eq1688 eq2883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688 eq2883
  have eq15431 : ∀ X0 X2 X3 : G, (τ (M.op X3 X3)) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3044 X3 (M.op x x) X2
       have i₂ := eq3044 X0 x (M.op x x)
       grind)
    | exact superpose eq3044 eq3044
    | exact resolve eq3044 eq3044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044
  have eq87910 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1693 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq88014 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87910 X2 X1
       have i₂ := eq1564 X0 X1
       grind)
    | exact superpose eq1564 eq87910
    | (have j0 := eq87910 X2 X1
       grind)
    | (have r₁ := eq87910 X0 (M.op X0 X0)
       have r₂ := eq1564 X0 (M.op X0 X0)
       grind)
    | exact resolve eq87910 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq214422 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq11091 eq1452
    | exact resolve eq1452 eq11091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq11091
  have eq214433 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq214422
       have r₂ := eq27
       grind)
    | exact resolve eq214422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214422
  have eq214466 : (τ (σ x)) = (k x (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq214433 eq1327
    | exact resolve eq1327 eq214433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327 eq214433
  have eq214749 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq214466
    | exact resolve eq214466 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214466
  have eq214830 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq88014 x x x
       grind)
    | (have r₁ := eq214749
       have r₂ := eq88014 x x x
       grind)
    | exact resolve eq214749 eq88014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88014 eq214749
  have eq214909 : ∀ X0 X1 : G, (k X0 X0) = (M.op x X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq3099 x X1 X0
       have i₂ := eq214830
       grind)
    | exact superpose eq214830 eq3099
    | exact resolve eq3099 eq214830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099
  have eq215007 : ∀ X0 : G, x ≠ x ∨ x = (k X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq87910 X0 x
       have i₂ := eq214830
       grind)
    | exact superpose eq214830 eq87910
    | (have j0 := eq87910 X0 x
       grind)
    | (have r₁ := eq87910 X0 x
       have r₂ := eq214830
       grind)
    | exact resolve eq87910 eq214830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87910 eq214830
  have eq215024 : ∀ X0 : G, x = (k X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq215007 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215007
  have eq215096 : ∀ X1 : G, x = (M.op x X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq215024 eq214909
    | exact resolve eq214909 eq215024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214909 eq215024
  have eq217376 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq215096 y
       grind)
    | exact superpose eq215096 eq18
    | (have j1 := eq215096 y
       grind)
    | exact resolve eq18 eq215096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215096
  have eq217577 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq217376
  have eq217730 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq217577 eq1567
    | exact resolve eq1567 eq217577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq217845 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq217730
    | (have j0 := eq217730 X0 X1
       grind)
    | exact resolve eq217730 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217730
  have eq217911 : ∀ X0 X1 : G, (k X1 X1) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq217577 eq217845
    | exact resolve eq217845 eq217577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217845
  have eq218322 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq217911 eq26
    | (have j1 := eq217911 (σ y) X0
       grind)
    | exact resolve eq26 eq217911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218562 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq217577 eq218322
    | exact resolve eq218322 eq217577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217577 eq218322
  have eq219084 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq217911 X1 x
       have i₂ := eq218562 x
       grind)
    | exact superpose eq218562 eq217911
    | exact resolve eq217911 eq218562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217911
  have eq219120 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq218562 sF3
       grind)
    | exact superpose eq218562 eq115
    | exact resolve eq115 eq218562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq219126 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq219084 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219084
  have eq219133 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq219120
    | exact resolve eq219120 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq219120
  have eq219403 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq218562 eq219133
    | exact resolve eq219133 eq218562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218562 eq219133
  have eq219969 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq219403
       grind)
    | exact superpose eq219403 eq18
    | exact resolve eq18 eq219403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219989 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq219403
  have eq224154 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq219969 eq219126
    | exact resolve eq219126 eq219969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219126 eq219969
  have eq224178 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq224154
  have eq224181 : x = (M.op x y) := by
    first
    | (have r₁ := eq224178
       have r₂ := eq219989
       grind)
    | exact resolve eq224178 eq219989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219989 eq224178
  have eq224184 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq224181
       grind)
    | exact superpose eq224181 eq18
    | exact resolve eq18 eq224181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq224185 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq224181
       grind)
    | exact superpose eq224181 eq22
    | exact resolve eq22 eq224181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq224181
  have eq224199 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq224185 eq20
    | exact resolve eq20 eq224185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224185
  have eq227591 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq224184 eq178
    | exact resolve eq178 eq224184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq228141 : ∀ X0 X2 X3 : G, (σ (M.op X3 X3)) = (τ (M.op (M.op (M.op x y) X0) X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq5366 x X2 X3
       have i₂ := eq227591 x X0
       grind)
    | (have i₁ := eq5366 (M.op x y) x X2
       have i₂ := eq227591 X0 (M.op x y)
       grind)
    | exact superpose eq227591 eq5366
    | exact resolve eq5366 eq227591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5366
  have eq228152 : ∀ X0 X1 X3 : G, (τ (M.op X1 X1)) = (τ (M.op (M.op (M.op x y) X0) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq5776 x X3 X1
       have i₂ := eq227591 x X0
       grind)
    | (have i₁ := eq5776 (M.op x y) X1 x
       have i₂ := eq227591 X0 (M.op x y)
       grind)
    | exact superpose eq227591 eq5776
    | exact resolve eq5776 eq227591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5776
  have eq228227 : ∀ X0 X2 X3 X4 : G, (M.op (τ (M.op (M.op X2 X2) X3)) X4) = (M.op (M.op x y) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq7949 X2 X3 x X4
       have i₂ := eq227591 x X0
       grind)
    | (have i₁ := eq7949 X0 x (M.op x y) X4
       have i₂ := eq227591 X0 (M.op x y)
       grind)
    | exact superpose eq227591 eq7949
    | exact resolve eq7949 eq227591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7949
  have eq228244 : ∀ X0 X1 X3 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op (M.op x y) X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq13124 x X3 X1
       have i₂ := eq227591 x X0
       grind)
    | (have i₁ := eq13124 (M.op x y) x X3
       have i₂ := eq227591 X0 (M.op x y)
       grind)
    | exact superpose eq227591 eq13124
    | exact resolve eq13124 eq227591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13124
  have eq228246 : ∀ X0 X1 X3 : G, (τ (M.op X1 X1)) = (M.op (σ (M.op (M.op x y) X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq13603 x X3 X1
       have i₂ := eq227591 x X0
       grind)
    | (have i₁ := eq13603 (M.op x y) X1 X3
       have i₂ := eq227591 X0 (M.op x y)
       grind)
    | exact superpose eq227591 eq13603
    | exact resolve eq13603 eq227591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13603
  have eq228252 : ∀ X0 X1 X3 : G, (τ (M.op X1 X1)) = (M.op (τ (M.op (M.op x y) X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq15431 x X3 X1
       have i₂ := eq227591 x X0
       grind)
    | (have i₁ := eq15431 (M.op x y) x X3
       have i₂ := eq227591 X0 (M.op x y)
       grind)
    | exact superpose eq227591 eq15431
    | exact resolve eq15431 eq227591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15431
  have eq228269 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq176 X2 X2 X3 X1 X4 X5
       have i₂ := eq227591 X2 X0
       grind)
    | (have i₁ := eq176 (M.op x y) X1 X2 X3 X4 X5
       have i₂ := eq227591 X0 X1
       grind)
    | exact superpose eq227591 eq176
    | exact resolve eq176 eq227591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq228274 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op (M.op x y) X0) X2) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq264 X2 X2 X3 X1 X4
       have i₂ := eq227591 X2 X0
       grind)
    | (have i₁ := eq264 (M.op x y) X1 X2 X3 x
       have i₂ := eq227591 X0 X1
       grind)
    | exact superpose eq227591 eq264
    | exact resolve eq264 eq227591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq228732 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq227591 eq224184
    | exact resolve eq224184 eq227591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224184 eq227591
  have eq228963 : ∀ X0 X2 X3 X4 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x y) X0) X2) X3) X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq228274 X0 x X2 X3 X4
       have i₂ := eq228732 x
       grind)
    | exact superpose eq228732 eq228274
    | exact resolve eq228274 eq228732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228274
  have eq228965 : ∀ X0 X2 X3 X4 X5 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X2) X3) X4) X5) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq228269 X0 x X2 X3 X4 X5
       have i₂ := eq228732 x
       grind)
    | exact superpose eq228732 eq228269
    | exact resolve eq228269 eq228732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228269
  have eq228970 : ∀ X0 X3 : G, (τ (M.op x y)) = (M.op (τ (M.op (M.op x y) X0)) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq228252 X0 x X3
       have i₂ := eq228732 x
       grind)
    | exact superpose eq228732 eq228252
    | exact resolve eq228252 eq228732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228252
  have eq228976 : ∀ X0 X3 : G, (τ (M.op x y)) = (M.op (σ (M.op (M.op x y) X0)) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq228246 X0 x X3
       have i₂ := eq228732 x
       grind)
    | exact superpose eq228732 eq228246
    | exact resolve eq228246 eq228732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228246
  have eq228978 : ∀ X0 X3 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) X0)) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq228244 X0 x X3
       have i₂ := eq228732 x
       grind)
    | exact superpose eq228732 eq228244
    | exact resolve eq228244 eq228732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228244
  have eq228989 : ∀ X0 X3 X4 : G, (M.op (M.op x y) X0) = (M.op (τ (M.op (M.op x y) X3)) X4) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq228227 X0 x X3 X4
       have i₂ := eq228732 x
       grind)
    | exact superpose eq228732 eq228227
    | exact resolve eq228227 eq228732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228227
  have eq229029 : ∀ X0 X3 : G, (τ (M.op x y)) = (τ (M.op (M.op (M.op x y) X0) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq228152 X0 x X3
       have i₂ := eq228732 x
       grind)
    | exact superpose eq228732 eq228152
    | exact resolve eq228152 eq228732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228152
  have eq229037 : ∀ X0 X2 : G, (σ (M.op x y)) = (τ (M.op (M.op (M.op x y) X0) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq228141 X0 X2 x
       have i₂ := eq228732 x
       grind)
    | exact superpose eq228732 eq228141
    | exact resolve eq228141 eq228732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228141 eq228732
  have eq229150 : ∀ X5 : G, (M.op x y) = (M.op (M.op x y) X5) := by
    intro X5
    first
    | exact superpose eq228963 eq228965
    | exact resolve eq228965 eq228963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228963 eq228965
  have eq229155 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq228976 eq228978
    | exact resolve eq228978 eq228976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228976 eq228978
  have eq229161 : ∀ X0 : G, (τ (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq228970 eq228989
    | exact resolve eq228989 eq228970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228970 eq228989
  have eq229178 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq229029 eq229037
    | exact resolve eq229037 eq229029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229029 eq229037
  have eq229222 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq20 eq229155
    | exact resolve eq229155 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229155
  have eq229226 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq229150 eq229161
    | exact resolve eq229161 eq229150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229161
  have eq229242 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq20 eq229178
    | exact resolve eq229178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq229178
  have eq229282 : (σ x) = (τ (M.op x y)) := by
    first
    | exact superpose eq224199 eq229222
    | exact resolve eq229222 eq224199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224199 eq229222
  have eq229290 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq229226 eq229242
    | exact resolve eq229242 eq229226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229242
  have eq229312 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq229226 eq229282
    | exact resolve eq229282 eq229226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229226 eq229282
  have eq229367 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq229312 eq26
    | exact resolve eq26 eq229312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq229312
  have eq229409 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq229150 eq229367
    | exact resolve eq229367 eq229150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229150 eq229367
  have eq229418 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq229409 eq27
    | exact resolve eq27 eq229409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq229409
  have eq229527 : False := by grind
  exact eq229527
