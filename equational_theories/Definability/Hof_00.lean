import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pyx_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X0) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X2)) (M.op X1 X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X2 X1) X3) (M.op X3 X1)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X2 X1) (M.op X1 (M.op X2 x))
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op (M.op X1 (M.op X2 X1)) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X1) X1 (M.op X2 x)
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X2 X1) X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq45 X2 (M.op x X1) (M.op X2 X1)
       have i₂ := eq45 X1 x X2
       grind)
    | exact superpose eq45 eq45
    | exact resolve eq45 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq124 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq124 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq124 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq126 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq23
    | exact resolve eq23 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq15
    | exact resolve eq15 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq127 X0
       have i₂ := eq125 (σ X0)
       grind)
    | exact superpose eq125 eq127
    | exact resolve eq127 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq129 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq126 X0
       have i₂ := eq125 (τ X0)
       grind)
    | exact superpose eq125 eq126
    | exact resolve eq126 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq126
  have eq130 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq128 X0
       grind)
    | exact superpose eq128 eq10
    | exact resolve eq10 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq231 X0 X1
       grind)
    | exact superpose eq231 eq15
    | (have j1 := eq231 X0 X1
       grind)
    | exact resolve eq15 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq233 x y
       grind)
    | exact superpose eq233 eq16
    | (have j1 := eq233 x y
       grind)
    | exact resolve eq16 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq257 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq242
       have i₂ := eq231 (σ x) (σ y)
       grind)
    | exact superpose eq231 eq242
    | (have j1 := eq231 x y
       grind)
    | (have r₁ := eq242
       have r₂ := eq231 (σ x) (σ y)
       grind)
    | exact resolve eq242 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq242
  have eq258 : (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq257
  have eq273 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq128 y
       have i₂ := eq258
       grind)
    | exact superpose eq258 eq128
    | exact resolve eq128 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq276 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq273
       have i₂ := eq128 x
       grind)
    | exact superpose eq128 eq273
    | exact resolve eq273 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq277 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq276
  have eq284 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ y)) (σ y)) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq45 (σ y) X0 (σ y)
       have i₂ := eq277
       grind)
    | exact superpose eq277 eq45
    | exact resolve eq45 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq129 (σ y)
       have i₂ := eq277
       grind)
    | exact superpose eq277 eq129
    | exact resolve eq129 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0
       have i₂ := eq277
       grind)
    | exact superpose eq277 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq277
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq277
       grind)
    | exact resolve eq13 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq298 : (M.op y y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq293
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq293
    | exact resolve eq293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq300 : (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq298
       have i₂ := eq130 x
       grind)
    | exact superpose eq130 eq298
    | exact resolve eq298 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq301 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq300
       grind)
    | exact superpose eq300 eq9
    | exact resolve eq9 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 : G, (M.op (M.op (M.op x x) X0) (M.op X0 y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq45 y y X0
       have i₂ := eq300
       grind)
    | exact superpose eq300 eq45
    | exact resolve eq45 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : (M.op x x) = (M.op y (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq50 y y
       have i₂ := eq300
       grind)
    | exact superpose eq300 eq50
    | exact resolve eq50 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = X0 ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq300
       grind)
    | exact superpose eq300 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq300
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq300
       grind)
    | exact resolve eq13 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X1 : G, (M.op x (M.op x X1)) = (M.op x (M.op (M.op x (M.op x X1)) y)) := by
    intro X1
    first
    | (have i₁ := eq44 x x X1 (M.op y (M.op y x))
       have i₂ := eq301 x
       grind)
    | exact superpose eq301 eq44
    | exact resolve eq44 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq301
  have eq2908 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq317 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq2914 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq2908
       grind)
    | exact superpose eq2908 eq15
    | exact resolve eq15 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2922 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2914
       grind)
    | exact superpose eq2914 eq16
    | exact resolve eq16 eq2914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2914
  have eq19098 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j0 := eq296 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq19102 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2922
       have i₂ := eq19098
       grind)
    | exact superpose eq19098 eq2922
    | (have r₁ := eq2922
       have r₂ := eq19098
       grind)
    | exact resolve eq2922 eq19098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922 eq19098
  have eq19106 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19102
  have eq19113 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq284 (σ x)
       have i₂ := eq19106
       grind)
    | exact superpose eq19106 eq284
    | exact resolve eq284 eq19106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq19116 : ∀ X0 : G, x = (M.op x y) ∨ (M.op (M.op (σ x) X0) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq19106
       grind)
    | exact superpose eq19106 eq9
    | exact resolve eq9 eq19106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19117 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq19106
       grind)
    | exact superpose eq19106 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19106
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19106
       grind)
    | exact resolve eq12 eq19106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19123 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50 (σ y) (σ x)
       have i₂ := eq19106
       grind)
    | exact superpose eq19106 eq50
    | exact resolve eq50 eq19106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19185 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19117
  have eq19211 : ∀ X0 : G, x = (M.op (M.op y x) y) ∨ (M.op (M.op (σ x) X0) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq46 y x
       have i₂ := eq19116 X0
       grind)
    | exact superpose eq19116 eq46
    | (have j1 := eq19116 X0
       grind)
    | exact resolve eq46 eq19116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19212 : ∀ X0 : G, x = (M.op x (M.op x x)) ∨ (M.op (M.op (σ x) X0) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 y x
       have i₂ := eq19116 X0
       grind)
    | exact superpose eq19116 eq50
    | (have j1 := eq19116 X0
       grind)
    | exact resolve eq50 eq19116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq19478 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq46 y x
       have i₂ := eq19123
       grind)
    | exact superpose eq19123 eq46
    | exact resolve eq46 eq19123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19123
  have eq19547 : (k (τ (σ y)) (τ (σ x))) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23 (σ x) (σ y)
       have i₂ := eq19185
       grind)
    | exact superpose eq19185 eq23
    | exact resolve eq23 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19185
  have eq19550 : (k (τ (σ y)) x) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19547
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19547
    | exact resolve eq19547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19547
  have eq19551 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19550
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq19550
    | exact resolve eq19550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19550
  have eq19742 : ∀ X0 : G, y = (M.op x (M.op y x)) ∨ (M.op (M.op (σ x) X0) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq45 x y y
       have i₂ := eq19211 X0
       grind)
    | exact superpose eq19211 eq45
    | (have j1 := eq19211 X0
       grind)
    | exact resolve eq45 eq19211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19211
  have eq19835 : ∀ X0 : G, x = (M.op x (M.op x y)) ∨ (M.op (M.op (σ x) X0) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq384 x
       have i₂ := eq19212 X0
       grind)
    | exact superpose eq19212 eq384
    | (have j1 := eq19212 X0
       grind)
    | exact resolve eq384 eq19212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq19212
  have eq20573 : ∀ X0 X1 : G, x = (M.op x x) ∨ (M.op (M.op (σ x) X0) (M.op X0 (σ x))) = X0 ∨ (M.op (M.op (σ x) X1) (M.op X1 (σ x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19835 X0
       have i₂ := eq19116 X1
       grind)
    | exact superpose eq19116 eq19835
    | (have j0 := eq19835 X0
       have j1 := eq19116 X0
       grind)
    | exact resolve eq19835 eq19116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19835
  have eq20667 : ∀ X1 : G, x = (M.op x x) ∨ (M.op (M.op (σ x) X1) (M.op X1 (σ x))) = X1 := by
    intro X1
    first
    | (have j0 := eq20573 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20573
  have eq20674 : ∀ X0 : G, x = (M.op y (M.op x y)) ∨ (M.op (M.op (σ x) X0) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq307
       have i₂ := eq20667 x
       grind)
    | exact superpose eq20667 eq307
    | (have j1 := eq20667 X0
       grind)
    | exact resolve eq307 eq20667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq22219 : ∀ X0 X1 : G, x = (M.op y x) ∨ (M.op (M.op (σ x) X0) (M.op X0 (σ x))) = X0 ∨ (M.op (M.op (σ x) X1) (M.op X1 (σ x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20674 X0
       have i₂ := eq19116 X1
       grind)
    | exact superpose eq19116 eq20674
    | (have j0 := eq20674 X0
       have j1 := eq19116 X0
       grind)
    | exact resolve eq20674 eq19116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19116 eq20674
  have eq22316 : ∀ X1 : G, x = (M.op y x) ∨ (M.op (M.op (σ x) X1) (M.op X1 (σ x))) = X1 := by
    intro X1
    first
    | (have j0 := eq22219 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22219
  have eq22325 : ∀ X0 X1 : G, y = (M.op x x) ∨ (M.op (M.op (σ x) X0) (M.op X0 (σ x))) = X0 ∨ (M.op (M.op (σ x) X1) (M.op X1 (σ x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19742 X0
       have i₂ := eq22316 X1
       grind)
    | exact superpose eq22316 eq19742
    | (have j0 := eq19742 X0
       have j1 := eq22316 X0
       grind)
    | exact resolve eq19742 eq22316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19742 eq22316
  have eq22415 : ∀ X1 : G, y = (M.op x x) ∨ (M.op (M.op (σ x) X1) (M.op X1 (σ x))) = X1 := by
    intro X1
    first
    | (have j0 := eq22325 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22325
  have eq22476 : ∀ X0 X1 : G, x = y ∨ (M.op (M.op (σ x) X0) (M.op X0 (σ x))) = X0 ∨ (M.op (M.op (σ x) X1) (M.op X1 (σ x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20667 X0
       have i₂ := eq22415 X1
       grind)
    | exact superpose eq22415 eq20667
    | (have j0 := eq20667 X0
       have j1 := eq22415 X0
       grind)
    | exact resolve eq20667 eq22415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20667 eq22415
  have eq22554 : ∀ X1 : G, (M.op (M.op (σ x) X1) (M.op X1 (σ x))) = X1 ∨ x = y := by
    intro X1
    first
    | (have j0 := eq22476 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22476
  have eq22664 : (τ (σ x)) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) ∨ x = y := by
    first
    | (have i₁ := eq129 (M.op (σ x) (σ x))
       have i₂ := eq22554 (σ x)
       grind)
    | exact superpose eq22554 eq129
    | exact resolve eq129 eq22554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq22554
  have eq22736 : (M.op (M.op x x) (M.op x x)) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq22664
       have i₂ := eq130 x
       grind)
    | exact superpose eq130 eq22664
    | exact resolve eq22664 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22664
  have eq22738 : x = (M.op (M.op x x) (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq22736
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22736
    | exact resolve eq22736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22736
  have eq26126 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19113
       have i₂ := eq19106
       grind)
    | exact superpose eq19106 eq19113
    | exact resolve eq19113 eq19106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19106 eq19113
  have eq26227 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq26126
  have eq26284 : (k y x) = (τ (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19551
       have i₂ := eq26227
       grind)
    | exact superpose eq26227 eq19551
    | exact resolve eq19551 eq26227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19551
  have eq26293 : y = (τ (M.op (σ x) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26227
       grind)
    | exact superpose eq26227 eq10
    | exact resolve eq10 eq26227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26227
  have eq26296 : (k y x) = (τ (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq26284
  have eq26306 : (τ (M.op (σ x) (σ x))) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26296
       have i₂ := eq46 (σ x) (σ x)
       grind)
    | (have i₁ := eq26296
       have i₂ := eq46 (σ x) (M.op (σ x) (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq46 eq26296
    | exact resolve eq26296 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26296
  have eq26309 : (M.op x x) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26306
       have i₂ := eq130 x
       grind)
    | exact superpose eq130 eq26306
    | exact resolve eq26306 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq26306
  have eq26320 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2908
       have i₂ := eq26309
       grind)
    | exact superpose eq26309 eq2908
    | exact resolve eq2908 eq26309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908 eq26309
  have eq26324 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq26320
  have eq26424 : x ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  have eq26758 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq26293
       have i₂ := eq19478
       grind)
    | exact superpose eq19478 eq26293
    | exact resolve eq26293 eq19478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19478 eq26293
  have eq26764 : x = (M.op x y) ∨ x = y ∨ x = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq26758
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26758
    | exact resolve eq26758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26758
  have eq26805 : x = (M.op (M.op y x) y) ∨ x = y ∨ x = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq46 y x
       have i₂ := eq26764
       grind)
    | exact superpose eq26764 eq46
    | exact resolve eq46 eq26764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq26764
  have eq26868 : x = (M.op (M.op y x) y) ∨ x = y := by grind
  clear eq26805
  have eq26921 : ∀ X0 : G, x = y ∨ (M.op (M.op x X0) (M.op X0 y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq45 y (M.op y x) X0
       have i₂ := eq26868
       grind)
    | exact superpose eq26868 eq45
    | exact resolve eq45 eq26868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq26868
  have eq27195 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (M.op x X0) (M.op X0 y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq26921 X0
       grind)
    | exact superpose eq26921 eq16
    | (have j1 := eq26921 X0
       grind)
    | exact resolve eq16 eq26921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26921
  have eq27384 : ∀ X0 : G, (M.op (M.op x X0) (M.op X0 y)) = X0 := by
    intro X0
    first
    | (have j0 := eq27195 X0
       grind)
    | (have r₁ := eq27195 X0
       have r₂ := eq128 x
       grind)
    | exact resolve eq27195 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27195
  have eq27457 : y = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq27384 y
       have i₂ := eq300
       grind)
    | exact superpose eq300 eq27384
    | exact resolve eq27384 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq27461 : (M.op x y) = (M.op x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq304 (M.op x y)
       have i₂ := eq27384 x
       grind)
    | exact superpose eq27384 eq304
    | exact resolve eq304 eq27384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq27384
  have eq27738 : x = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq27461
       have i₂ := eq26324
       grind)
    | exact superpose eq26324 eq27461
    | exact resolve eq27461 eq26324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27461
  have eq28435 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq27738
       have i₂ := eq26324
       grind)
    | exact superpose eq26324 eq27738
    | exact resolve eq27738 eq26324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26324 eq27738
  have eq28530 : x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq28435
  have eq28538 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq28530
       have r₂ := eq26424
       grind)
    | exact resolve eq28530 eq26424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26424 eq28530
  have eq28570 : y = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq27457
       have i₂ := eq28538
       grind)
    | exact superpose eq28538 eq27457
    | exact resolve eq27457 eq28538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27457 eq28538
  have eq28668 : x = y ∨ x = y := by
    first
    | (have i₁ := eq22738
       have i₂ := eq28570
       grind)
    | exact superpose eq28570 eq22738
    | exact resolve eq22738 eq28570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22738 eq28570
  have eq28782 : x = y := by grind
  clear eq28668
  have eq28789 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28782
       grind)
    | exact superpose eq28782 eq16
    | exact resolve eq16 eq28782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28782
  have eq28970 : False := by grind
  exact eq28970

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq60
  have eq83 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq90
  have eq285 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq288 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq285 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq292 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq288 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq288 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq288 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq303 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq292 X0 X1
       have j1 := eq83 X1 (σ X0)
       grind)
    | (have r₁ := eq292 X0 X0
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq292 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq292
  have eq311 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq303
    | (have j0 := eq303 X0 X1
       grind)
    | exact resolve eq303 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq312 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq311 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq318 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq312 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq312
    | exact resolve eq312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq312 x y
       grind)
    | exact superpose eq312 eq16
    | exact resolve eq16 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq406 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq318 X0 (τ X1)
       grind)
    | exact superpose eq318 eq18
    | exact resolve eq18 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq318
  have eq419 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq406
    | exact resolve eq406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq425 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq419
    | exact resolve eq419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq437 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq329
       have i₂ := eq425 x y
       grind)
    | exact superpose eq425 eq329
    | exact resolve eq329 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq425
  have eq438 : False := by grind
  exact eq438

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_x_pyx_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq53 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq111 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq111 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq112 X0 X1 X2
       have j1 := eq13 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | (have r₁ := eq112 X0 X1 X2
       have r₂ := eq13 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq131 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq336 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq350 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq113
    | exact resolve eq113 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) (M.op X0 X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq61 X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X4 X5
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X2 (M.op (M.op X2 X0) X3)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 (M.op X0 X1) (M.op X2 (M.op (M.op X2 X0) X3)) X0
       have i₂ := eq61 X0 X2 X3 X1
       grind)
    | exact superpose eq61 eq113
    | exact resolve eq113 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq428 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq428 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq428
    | exact resolve eq428 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq435 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X1 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq427
    | exact resolve eq427 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq438 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq416 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq416
    | exact resolve eq416 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq444 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq434 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq434
    | (have j0 := eq434 x y
       grind)
    | exact resolve eq434 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq444 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq444
       grind)
    | exact resolve eq12 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq444 eq14
    | exact resolve eq14 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : x = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq470
  have eq473 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq472
       have r₂ := eq13 x x
       grind)
    | exact resolve eq472 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq483 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq473 eq129
    | exact resolve eq129 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq485 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq483
    | exact resolve eq483 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq528 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq72 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq72 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq72 X0 X1
       grind)
    | exact resolve eq13 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (M.op X2 (M.op (M.op X2 (σ X0)) X3)) (σ (k X0 X1))) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (σ X0) X2 X3 (σ X1)
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq61
    | (have j1 := eq72 X0 X1
       grind)
    | exact resolve eq61 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq537 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq539 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq528 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq541 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq539 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq539 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq539 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq1324 : ∀ X0 : G, (σ y) ≠ (k (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq541 y X0
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq541
    | (have j0 := eq541 y X0
       grind)
    | exact resolve eq541 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq1328 : ∀ X0 : G, (σ y) ≠ (k (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1324 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1324
    | (have j0 := eq1324 X0
       grind)
    | exact resolve eq1324 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1334 : ∀ X0 : G, (σ y) ≠ (k (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1328 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1328
    | (have j0 := eq1328 X0
       grind)
    | exact resolve eq1328 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq3479 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq438 X1 (M.op (M.op X1 X0) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq438
    | exact resolve eq438 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3520 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq350 X0 X0 x X0
       have i₂ := eq438 X0 X0 x
       grind)
    | exact superpose eq438 eq350
    | exact resolve eq350 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq3521 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x X0
       have i₂ := eq438 X0 X0 x
       grind)
    | exact superpose eq438 eq61
    | exact resolve eq61 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3594 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq438 X0 X0 X0
       have i₂ := eq3521 X0
       grind)
    | exact superpose eq3521 eq438
    | exact resolve eq438 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3682 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq537 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq537
    | (have j0 := eq537 (τ X0)
       grind)
    | exact resolve eq537 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq537
  have eq3692 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3682 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3682
    | (have j0 := eq3682 X0
       grind)
    | exact resolve eq3682 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3682
  have eq3698 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3692 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3692
    | (have j0 := eq3692 X0
       grind)
    | exact resolve eq3692 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3692
  have eq4098 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq407 X0 X0 x X0 X2
       have i₂ := eq438 X0 X0 x
       grind)
    | exact superpose eq438 eq407
    | exact resolve eq407 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq6084 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq3594 X0
       grind)
    | exact superpose eq3594 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq3594 X0
       grind)
    | exact resolve eq13 eq3594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6102 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6084 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6084
  have eq6152 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 (M.op X1 X1)
       have i₂ := eq6102 X1 (σ X0)
       grind)
    | exact superpose eq6102 eq336
    | exact resolve eq336 eq6102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq6158 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6152 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq6152
    | exact resolve eq6152 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6152
  have eq6997 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq408 X0 X0 x X0 X2 X3
       have i₂ := eq438 X0 X0 x
       grind)
    | exact superpose eq438 eq408
    | exact resolve eq408 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq10601 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ y)) X1)) (k (σ y) (σ x))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq530 y x X0 X1
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq530
    | (have j0 := eq530 y x x x
       grind)
    | exact resolve eq530 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq10615 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) (k (σ (M.op x y)) (σ x))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq129 eq530
    | (have j0 := eq530 (M.op x y) x x x
       grind)
    | exact resolve eq530 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq530
  have eq10754 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) (k (σ (M.op x y)) (σ x))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq10615
    | (have j0 := eq10615 X0 X1
       grind)
    | exact resolve eq10615 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10615
  have eq10768 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ y)) X1)) (k (σ y) (σ x))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq10601 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10601
    | (have j0 := eq10601 X0 X1
       grind)
    | exact resolve eq10601 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10601
  have eq10897 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq485 eq10754
    | exact resolve eq10754 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10754
  have eq10911 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ y)) X1)) (k (σ y) (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq10768 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10768
    | (have j0 := eq10768 X0 X1
       grind)
    | exact resolve eq10768 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10768
  have eq10999 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10897 x x
       have i₂ := eq14 sF1 x x
       grind)
    | exact superpose eq14 eq10897
    | exact resolve eq10897 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10897
  have eq11012 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ y)) X1)) (k (σ y) (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq10911 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10911
    | (have j0 := eq10911 X0 X1
       grind)
    | exact resolve eq10911 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10911
  have eq11095 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq10999
    | exact resolve eq10999 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10999
  have eq11108 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ y)) X1)) (k (σ y) (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq11012
    | (have j0 := eq11012 X0 X1
       grind)
    | exact resolve eq11012 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11012
  have eq11171 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11095
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11095
    | exact resolve eq11095 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11095
  have eq11172 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ y)) X1)) (k (σ y) (σ x))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq11108 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11108
    | (have j0 := eq11108 X0 X1
       grind)
    | exact resolve eq11108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11108
  have eq11181 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq11171
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11171
    | exact resolve eq11171 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11171
  have eq28843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq28844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq28843
    | exact resolve eq28843 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28843
  have eq28855 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq28844
       have r₂ := eq27
       grind)
    | exact resolve eq28844 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28844
  have eq28870 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq28855 eq6158
    | exact resolve eq6158 eq28855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6158 eq28855
  have eq28928 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq28870
    | exact resolve eq28870 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28870
  have eq28940 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq28928 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq28928 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq28928 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28928
  have eq28969 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq435 X0 x
       have i₂ := eq28940 (M.op X0 x)
       grind)
    | exact superpose eq28940 eq435
    | (have j1 := eq28940 X0
       grind)
    | exact resolve eq435 eq28940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq28940
  have eq28979 : ∀ X0 : G, (τ (σ x)) = (k x y) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq53
       have i₂ := eq28969 (k sF2 sF3)
       grind)
    | exact superpose eq28969 eq53
    | (have j1 := eq28969 X0
       grind)
    | exact resolve eq53 eq28969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq28969
  have eq29006 : ∀ X0 : G, x = (k x y) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28 eq28979
    | (have j0 := eq28979 x
       grind)
    | exact resolve eq28979 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq28979
  have eq40476 : x ≠ x ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have j0 := eq29006 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29006
  have eq40477 : x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq40476
  have eq40616 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq40477
       grind)
    | exact superpose eq40477 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq40477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40477
  have eq40617 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq40616
  have eq40619 : y = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40617
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40617
    | exact resolve eq40617 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40617
  have eq41247 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq438 y y x
       have i₂ := eq40619
       grind)
    | exact superpose eq40619 eq438
    | exact resolve eq438 eq40619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41256 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq41247 X0
       have i₂ := eq434 y X0
       grind)
    | (have i₁ := eq41247 X0
       have i₂ := eq434 y (M.op y X0)
       grind)
    | exact superpose eq434 eq41247
    | exact resolve eq41247 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41247
  have eq92552 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq41256 X0
       grind)
    | exact superpose eq41256 eq14
    | exact resolve eq14 eq41256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41256
  have eq97118 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq92552 X0
       have i₂ := eq40619
       grind)
    | exact superpose eq40619 eq92552
    | exact resolve eq92552 eq40619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40619 eq92552
  have eq97237 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq97118 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97118
  have eq97290 : x ≠ x ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq97237 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97237
  have eq97291 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq97290
  have eq97331 : y = (M.op (M.op (M.op y y) x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4098 y x
       have i₂ := eq97291
       grind)
    | exact superpose eq97291 eq4098
    | exact resolve eq4098 eq97291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4098
  have eq97334 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op y y) x) (M.op y X0)) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6997 y x X0
       have i₂ := eq97291
       grind)
    | exact superpose eq97291 eq6997
    | exact resolve eq6997 eq97291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6997
  have eq99494 : (M.op (M.op y y) x) = (M.op (M.op (M.op y y) y) (M.op (M.op y y) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq438 (M.op y y) x y
       have i₂ := eq97331
       grind)
    | exact superpose eq97331 eq438
    | exact resolve eq438 eq97331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99529 : (M.op (M.op y y) x) = (M.op y (M.op (M.op y y) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99494
       have i₂ := eq3521 y
       grind)
    | exact superpose eq3521 eq99494
    | exact resolve eq99494 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521 eq99494
  have eq151566 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y (M.op x X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3479 x y x
       have i₂ := eq97291
       grind)
    | exact superpose eq97291 eq3479
    | exact resolve eq3479 eq97291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479 eq97291
  have eq447509 : (M.op y y) = (M.op (M.op (M.op y y) x) (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq438 y y x
       have i₂ := eq99529
       grind)
    | exact superpose eq99529 eq438
    | exact resolve eq438 eq99529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99529
  have eq604821 : x = (M.op (M.op (M.op y y) (M.op y y)) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x (M.op y y) (M.op y y)
       have i₂ := eq447509
       grind)
    | exact superpose eq447509 eq14
    | exact resolve eq14 eq447509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604822 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op y y) (M.op y y)) (M.op x X0)) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 x (M.op y y) (M.op y y) X0
       have i₂ := eq447509
       grind)
    | exact superpose eq447509 eq61
    | exact resolve eq61 eq447509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq447509
  have eq604974 : ∀ X0 : G, x = (M.op (M.op (M.op y y) (M.op x X0)) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq604822 X0
       have i₂ := eq3594 y
       grind)
    | exact superpose eq3594 eq604822
    | exact resolve eq604822 eq3594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604822
  have eq604975 : x = (M.op (M.op y y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq604821
       have i₂ := eq3594 y
       grind)
    | exact superpose eq3594 eq604821
    | exact resolve eq604821 eq3594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594 eq604821
  have eq605003 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97331
       have i₂ := eq604975
       grind)
    | exact superpose eq604975 eq97331
    | exact resolve eq97331 eq604975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97331
  have eq605005 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq97334 X0
       have i₂ := eq604975
       grind)
    | exact superpose eq604975 eq97334
    | exact resolve eq97334 eq604975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97334 eq604975
  have eq605177 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq605005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605005
  have eq605179 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq605003
  have eq605203 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq605179
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq605179
    | exact resolve eq605179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605179
  have eq605208 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq605203 eq20
    | exact resolve eq20 eq605203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605227 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq605203 eq131
    | exact resolve eq131 eq605203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq605203
  have eq605798 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq605227
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq605227
    | exact resolve eq605227 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq605227
  have eq605815 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq605208
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq605208
    | exact resolve eq605208 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605208
  have eq605817 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq605815 eq26
    | exact resolve eq26 eq605815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605968 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) (k (σ (M.op x y)) (σ x))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq605815 eq11172
    | exact resolve eq11172 eq605815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11172
  have eq606473 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) (k (σ (M.op x y)) (σ x))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq605968 X0 X1
       grind)
    | (have r₁ := eq605968 X0 X1
       have r₂ := eq27
       grind)
    | exact resolve eq605968 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605968
  have eq606546 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq485 eq606473
    | exact resolve eq606473 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq606473
  have eq606562 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq606546 x x
       have i₂ := eq14 sF1 x x
       grind)
    | exact superpose eq14 eq606546
    | exact resolve eq606546 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606546
  have eq621090 : ∀ X0 : G, (σ y) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq605798 eq1334
    | (have j0 := eq1334 X0
       grind)
    | exact resolve eq1334 eq605798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334 eq605798
  have eq692112 : ∀ X0 : G, y = (M.op (M.op y (M.op x X0)) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq605177 (M.op x X0)
       have i₂ := eq151566 X0
       grind)
    | exact superpose eq151566 eq605177
    | exact resolve eq605177 eq151566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151566 eq605177
  have eq692263 : ∀ X0 : G, y = (M.op (M.op y (M.op x X0)) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq692112 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692112
  have eq740680 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y y) (M.op x X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x X0) y y
       have i₂ := eq692263 X0
       grind)
    | exact superpose eq692263 eq14
    | exact resolve eq14 eq692263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692263
  have eq997090 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq606562 eq6102
    | exact resolve eq6102 eq606562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6102 eq606562
  have eq1043766 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3520 X0
       have i₂ := eq997090 (M.op X0 X0)
       grind)
    | exact superpose eq997090 eq3520
    | (have j1 := eq997090 X0
       grind)
    | exact resolve eq3520 eq997090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3520 eq997090
  have eq1054520 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (k X1 (σ x)) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq621090 X0
       have i₂ := eq1043766 (k sF1 sF1)
       grind)
    | exact superpose eq1043766 eq621090
    | (have j0 := eq621090 X0
       have j1 := eq1043766 X1
       grind)
    | exact resolve eq621090 eq1043766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621090 eq1043766
  have eq1054605 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1054520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054520
  have eq1054638 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1054605 X0 X1
       grind)
    | (have r₁ := eq1054605 X0 X1
       have r₂ := eq605815
       grind)
    | exact resolve eq1054605 eq605815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054605
  have eq1065106 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3698 X0
       have i₂ := eq1054638 (k X0 X0) x
       grind)
    | exact superpose eq1054638 eq3698
    | (have j0 := eq3698 (σ x)
       have j1 := eq1054638 X0 x
       grind)
    | (have r₁ := eq3698 (σ x)
       have r₂ := eq1054638 X0 (σ x)
       grind)
    | (have r₁ := eq3698 (σ y)
       have r₂ := eq1054638 (σ y) x
       grind)
    | exact resolve eq3698 eq1054638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054638
  have eq1065619 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1065106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065106
  have eq1653564 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq604974 X0
       have i₂ := eq740680 X0
       grind)
    | exact superpose eq740680 eq604974
    | exact resolve eq604974 eq740680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604974 eq740680
  have eq1653795 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1653564 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653564
  have eq1654254 : (σ x) = (M.op (M.op (M.op x x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq425 x x
       have i₂ := eq1653795 sF2
       grind)
    | exact superpose eq1653795 eq425
    | exact resolve eq425 eq1653795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq1654302 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq1653795 X0
       grind)
    | exact superpose eq1653795 eq14
    | exact resolve eq14 eq1653795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653795
  have eq1695811 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1654254
       have i₂ := eq1654302 sF4
       grind)
    | exact superpose eq1654302 eq1654254
    | exact resolve eq1654254 eq1654302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654254 eq1654302
  have eq1696040 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1695811
  have eq1696047 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1696040 eq60
    | exact resolve eq60 eq1696040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1696040
  have eq1698759 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1696047
       have i₂ := eq1065619 (M.op sF2 sF2)
       grind)
    | exact superpose eq1065619 eq1696047
    | (have j1 := eq1065619 X0
       grind)
    | exact resolve eq1696047 eq1065619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065619 eq1696047
  have eq1699007 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1698759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698759
  have eq1699103 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq1699007
    | (have j0 := eq1699007 X0
       grind)
    | exact resolve eq1699007 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699007
  have eq1742795 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq605815 eq1699103
    | exact resolve eq1699103 eq605815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605815 eq1699103
  have eq1744038 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1742795 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742795
  have eq1744576 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1744038 X0
       grind)
    | (have r₁ := eq1744038 X0
       have r₂ := eq27
       grind)
    | exact resolve eq1744038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744038
  have eq1745287 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1744576 eq3698
    | (have j0 := eq3698 (σ (M.op x y))
       grind)
    | (have r₁ := eq3698 (σ (M.op x y))
       have r₂ := eq1744576 (σ (M.op x y))
       grind)
    | exact resolve eq3698 eq1744576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3698 eq1744576
  have eq1745968 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1745287
  have eq1747646 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1745968 eq438
    | exact resolve eq438 eq1745968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq1747835 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1747646 X0
       have i₂ := eq434 sF1 (M.op sF1 X0)
       grind)
    | (have i₁ := eq1747646 x
       have i₂ := eq434 sF1 x
       grind)
    | exact superpose eq434 eq1747646
    | exact resolve eq1747646 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747646
  have eq2214758 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1747835 eq14
    | exact resolve eq14 eq1747835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2579494 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1745968 eq2214758
    | exact resolve eq2214758 eq1745968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745968 eq2214758
  have eq2580569 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2579494 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579494
  have eq2580658 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2580569 eq1747835
    | exact resolve eq1747835 eq2580569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747835 eq2580569
  have eq2581639 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2580658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580658
  have eq2586532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2581639 eq605817
    | exact resolve eq605817 eq2581639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605817 eq2581639
  have eq2586778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2586532
  have eq2586898 : x = (M.op x y) := by
    first
    | (have r₁ := eq2586778
       have r₂ := eq27
       grind)
    | exact resolve eq2586778 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586778
  have eq2586909 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2586898 eq20
    | exact resolve eq20 eq2586898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2586970 : x = (M.op x x) := by
    first
    | exact superpose eq2586898 eq444
    | exact resolve eq444 eq2586898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq2586972 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq2586898 eq471
    | exact resolve eq471 eq2586898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq2587594 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq2586972 X0
       have i₂ := eq434 x X0
       grind)
    | (have i₁ := eq2586972 X0
       have i₂ := eq434 x (M.op x X0)
       grind)
    | exact superpose eq434 eq2586972
    | exact resolve eq2586972 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq2586972
  have eq2587648 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2586909
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2586909
    | exact resolve eq2586909 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586909
  have eq2592174 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2587648 eq26
    | exact resolve eq26 eq2587648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2592437 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2587648 eq11181
    | exact resolve eq11181 eq2587648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11181
  have eq2592902 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2592437
  have eq2674655 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq2587594 X0
       grind)
    | exact superpose eq2587594 eq14
    | exact resolve eq14 eq2587594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587594
  have eq2675525 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2674655 X0
       have i₂ := eq2586970
       grind)
    | exact superpose eq2586970 eq2674655
    | exact resolve eq2674655 eq2586970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586970 eq2674655
  have eq2676280 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2675525 y
       grind)
    | exact superpose eq2675525 eq18
    | (have j1 := eq2675525 y
       grind)
    | exact resolve eq18 eq2675525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2675525
  have eq2678116 : x = y := by
    first
    | exact superpose eq2586898 eq2676280
    | exact resolve eq2676280 eq2586898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586898 eq2676280
  have eq2679496 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2678116
       grind)
    | exact superpose eq2678116 eq24
    | exact resolve eq24 eq2678116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2678116
  have eq2681070 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2679496
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2679496
    | exact resolve eq2679496 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2679496
  have eq2681315 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2587648 eq2681070
    | exact resolve eq2681070 eq2587648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587648 eq2681070
  have eq2682630 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2681315 eq2592174
    | exact resolve eq2592174 eq2681315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592174 eq2681315
  have eq2682640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2592902 eq2682630
    | exact resolve eq2682630 eq2592902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592902 eq2682630
  have eq2682930 : False := by grind
  exact eq2682930

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
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
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq645 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
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
  have eq659 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq668 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq678 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq645
       grind)
    | exact superpose eq645 eq40
    | exact resolve eq40 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq679 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq678
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq678
    | exact resolve eq678 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq681 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq679
    | exact resolve eq679 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq681 eq659
    | exact resolve eq659 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq681
  have eq698 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq691
       have r₂ := eq27
       grind)
    | exact resolve eq691 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq705 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq698 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq698
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq698
       grind)
    | exact resolve eq13 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq710 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq705
  have eq713 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq710 eq142
    | exact resolve eq142 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq710
  have eq716 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq713
    | exact resolve eq713 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq713
  have eq719 : x = (M.op x x) := by
    first
    | (have j1 := eq668 x
       grind)
    | (have r₁ := eq716
       have r₂ := eq668 x
       grind)
    | exact resolve eq716 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq723 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq178
    | exact resolve eq178 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq724 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq175
    | exact resolve eq175 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq725 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq719
       grind)
    | exact resolve eq13 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq16
    | exact resolve eq16 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq16 x x X0
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq16
    | exact resolve eq16 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq730 : x = (k x x) := by grind
  clear eq725
  have eq732 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq730
       grind)
    | exact superpose eq730 eq40
    | exact resolve eq40 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq730
  have eq735 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq732
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq732
    | exact resolve eq732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq732
  have eq740 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq735 eq668
    | (have j0 := eq668 (σ x)
       grind)
    | (have r₁ := eq668 (σ x)
       have r₂ := eq735
       grind)
    | exact resolve eq668 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq735
  have eq741 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq740
  have eq747 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq741 eq176
    | exact resolve eq176 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq741
  have eq783 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq723 eq726
    | exact resolve eq726 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq783 eq723
    | exact resolve eq723 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq783
  have eq801 : y = (M.op x y) := by
    first
    | exact superpose eq792 eq724
    | exact resolve eq724 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq792
  have eq806 : y = (M.op x y) := by
    first
    | (have i₁ := eq801
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq801
    | exact resolve eq801 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq801
  have eq808 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq24
    | exact resolve eq24 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq806
  have eq822 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq808 eq20
    | exact resolve eq20 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq808
  have eq910 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq726 (M.op x X0)
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq726
    | exact resolve eq726 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq727 X0
       have i₂ := eq910 X0
       grind)
    | exact superpose eq910 eq727
    | exact resolve eq727 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq910
  have eq941 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq726 X0
       have i₂ := eq925 X0
       grind)
    | exact superpose eq925 eq726
    | exact resolve eq726 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq925
  have eq962 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x X1
       have i₂ := eq941 X0
       grind)
    | exact superpose eq941 eq16
    | exact resolve eq16 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq962 X0 X1
       have i₂ := eq941 X1
       grind)
    | exact superpose eq941 eq962
    | exact resolve eq962 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq962
  have eq1283 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq965
    | (have j0 := eq965 (σ x) (σ y)
       grind)
    | exact resolve eq965 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq1316 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1283 eq747
    | exact resolve eq747 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq1283
  have eq1338 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1316 eq26
    | exact resolve eq26 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1316
  have eq1350 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1338 eq27
    | exact resolve eq27 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1338
  have eq1360 : False := by grind
  exact eq1360

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq42 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq185 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq359 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq185 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq185 X0 X1
       grind)
    | exact superpose eq185 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq185 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq185 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq185 X0 X1
       grind)
    | exact resolve eq13 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq370 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq359 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq371 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq373 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq371
    | (have j0 := eq371 X0 X1
       grind)
    | exact resolve eq371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq7188 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq373 X0 X1
       have j1 := eq369 X1 X0
       grind)
    | (have r₁ := eq373 X1 X0
       have r₂ := eq369 X0 X1
       grind)
    | (have r₁ := eq373 (k X1 X0) X1
       have r₂ := eq369 X0 X1
       grind)
    | (have r₁ := eq373 X1 X1
       have r₂ := eq369 X1 X1
       grind)
    | exact resolve eq373 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq373
  have eq7189 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7188 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7188
    | exact resolve eq7188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7222 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7188 y x
       grind)
    | exact superpose eq7188 eq16
    | (have j1 := eq7188 y x
       grind)
    | exact resolve eq16 eq7188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7188
  have eq7313 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7189 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq7189
    | (have j0 := eq7189 X0 X1
       grind)
    | exact resolve eq7189 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7189
  have eq7314 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7313 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7313
    | exact resolve eq7313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7313
  have eq7447 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq7314 (τ X1) X0
       grind)
    | exact superpose eq7314 eq18
    | (have j1 := eq7314 (τ X1) X0
       grind)
    | exact resolve eq18 eq7314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7691 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7447 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7447
    | exact resolve eq7447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7447
  have eq7837 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7691 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7691
    | (have j0 := eq7691 X0 X1
       grind)
    | exact resolve eq7691 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7691
  have eq7917 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7222
       have i₂ := eq7314 y x
       grind)
    | exact superpose eq7314 eq7222
    | (have j1 := eq7314 (σ y) (σ x)
       grind)
    | exact resolve eq7222 eq7314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7314
  have eq7922 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq7917
  have eq7929 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq7922
       grind)
    | exact superpose eq7922 eq36
    | exact resolve eq36 eq7922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq7978 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94 (σ x) (σ x)
       have i₂ := eq7922
       grind)
    | exact superpose eq7922 eq94
    | exact resolve eq94 eq7922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7922
  have eq8012 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7929
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq7929
    | exact resolve eq7929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7929
  have eq8018 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7837 y x
       have i₂ := eq8012
       grind)
    | exact superpose eq8012 eq7837
    | (have j0 := eq7837 y x
       grind)
    | exact resolve eq7837 eq8012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7837 eq8012
  have eq8027 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq8018
  have eq8234 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7978
       grind)
    | exact superpose eq7978 eq16
    | exact resolve eq16 eq7978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7978
  have eq8287 : y = (M.op x x) := by
    first
    | (have r₁ := eq8234
       have r₂ := eq8027
       grind)
    | exact resolve eq8234 eq8027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8027 eq8234
  have eq8289 : y = (k y x) := by grind
  have eq8332 : y = (M.op x y) := by
    first
    | (have i₁ := eq94 x x
       have i₂ := eq8287
       grind)
    | exact superpose eq8287 eq94
    | exact resolve eq94 eq8287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8287
  have eq8365 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7222
       have i₂ := eq8289
       grind)
    | exact superpose eq8289 eq7222
    | exact resolve eq7222 eq8289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7222 eq8289
  have eq11122 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8365
       have i₂ := eq8332
       grind)
    | exact superpose eq8332 eq8365
    | exact resolve eq8365 eq8332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8365
  have eq11123 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq11122
  have eq11181 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq94 (σ x) (σ x)
       have i₂ := eq11123
       grind)
    | exact superpose eq11123 eq94
    | exact resolve eq94 eq11123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq11123
  have eq11457 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11181
       grind)
    | exact superpose eq11181 eq16
    | exact resolve eq16 eq11181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11181
  have eq11513 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq11457
       have i₂ := eq8332
       grind)
    | exact superpose eq8332 eq11457
    | exact resolve eq11457 eq8332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8332 eq11457
  have eq11514 : False := by grind
  exact eq11514

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op (M.op X1 X0) (M.op X1 X2))) = X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq26 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq29 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  have eq41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq76 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37 y x
       grind)
    | exact superpose eq37 eq16
    | (have j1 := eq37 y x
       grind)
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq37 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 X3 X4 : G, (k X1 (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0)) = X1 ∨ (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0)) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq27 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3
       have i₂ := eq21 X0 X1 X2 X3
       grind)
    | exact superpose eq21 eq27
    | exact resolve eq27 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq27
  have eq304 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38
    | exact resolve eq38 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq13
    | (have j0 := eq13 X0 (τ X1)
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq38 X0 (τ X0)
       grind)
    | (have r₁ := eq13 (M.op (τ X0) (τ X0)) X1
       have r₂ := eq38 X0 (M.op X1 (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq13 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq321 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq322 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq312 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq323 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq322 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq325 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq321 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq321
    | (have j0 := eq321 X0
       grind)
    | exact resolve eq321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq331 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq304
    | (have j0 := eq304 X0 X1
       grind)
    | exact resolve eq304 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq105
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq428 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq427
  have eq905 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq76 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq924 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq905 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq905
    | exact resolve eq905 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq2167 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 (τ X1) (τ X0)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq114
    | (have j0 := eq114 (τ X1) (τ X0)
       grind)
    | exact resolve eq114 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2198 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2167 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2167
    | (have j0 := eq2167 X0 X1
       grind)
    | exact resolve eq2167 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq2205 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2198 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2198
    | (have j0 := eq2198 X0 X1
       grind)
    | exact resolve eq2198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2211 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2205 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2205
    | (have j0 := eq2205 X0 X1
       grind)
    | exact resolve eq2205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq2216 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2211 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2211
    | (have j0 := eq2211 X0 X1
       grind)
    | exact resolve eq2211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq2221 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2216 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2216
    | (have j0 := eq2216 X0 X1
       grind)
    | exact resolve eq2216 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq2226 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2221 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2221
    | (have j0 := eq2221 X0 X1
       grind)
    | exact resolve eq2221 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq3565 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (k (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X0) ∨ (M.op X0 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq143 X0 (M.op (M.op (M.op (M.op X2 X0) (M.op X2 x)) X0) X2) X2 X0 x
       have i₂ := eq9 X0 (M.op (M.op (M.op X2 X0) (M.op X2 x)) X0) X2
       grind)
    | exact superpose eq9 eq143
    | exact resolve eq143 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq3590 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k (M.op X0 X3) X0) ∨ (M.op X0 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3565 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq3565
    | (have j0 := eq3565 X0 X1 X2 X3
       grind)
    | exact resolve eq3565 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3565
  have eq3592 : ∀ X0 X3 : G, (M.op X0 X3) = (k (M.op X0 X3) X0) ∨ (M.op X0 X0) = (M.op X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq3590 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq3590
    | (have j0 := eq3590 X0 x x X3
       grind)
    | exact resolve eq3590 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3590
  have eq3737 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq325 X0
       grind)
    | exact superpose eq325 eq10
    | (have j1 := eq325 X0
       grind)
    | exact resolve eq10 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq4280 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq3737 X0
       grind)
    | exact superpose eq3737 eq29
    | (have j1 := eq3737 X0
       grind)
    | exact resolve eq29 eq3737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq4332 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3737
  have eq4357 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4280 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4280
    | (have j0 := eq4280 X0
       grind)
    | exact resolve eq4280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4280
  have eq4401 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq4357 (σ X0)
       grind)
    | exact superpose eq4357 eq34
    | (have j1 := eq4357 (σ X0)
       grind)
    | exact resolve eq34 eq4357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4357
  have eq4424 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4401 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4401
    | (have j0 := eq4401 X0
       grind)
    | exact resolve eq4401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4401
  have eq4443 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (τ (σ X0)) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4424 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq4424
    | (have j0 := eq4424 X0
       grind)
    | exact resolve eq4424 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4424
  have eq4461 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4443 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4443
    | (have j0 := eq4443 X0
       grind)
    | exact resolve eq4443 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq7372 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq323
    | exact resolve eq323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq7467 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7372 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7372
    | (have j0 := eq7372 X0 X1
       grind)
    | exact resolve eq7372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7372
  have eq7553 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4332 (σ X0)
       have i₂ := eq34 X0 (σ X0)
       grind)
    | exact superpose eq34 eq4332
    | exact resolve eq4332 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4332
  have eq7558 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7553 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7553
    | (have j0 := eq7553 X0
       grind)
    | exact resolve eq7553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7553
  have eq7561 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq7558 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7558
    | (have j0 := eq7558 X0
       grind)
    | exact resolve eq7558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7558
  have eq7564 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7561 X0
       have j1 := eq4461 X0
       grind)
    | (have r₁ := eq7561 X0
       have r₂ := eq4461 X0
       grind)
    | exact resolve eq7561 eq4461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4461 eq7561
  have eq7725 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7564 (σ X0)
       grind)
    | exact superpose eq7564 eq15
    | exact resolve eq15 eq7564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7731 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0 X0
       have i₂ := eq7564 (τ X0)
       grind)
    | exact superpose eq7564 eq41
    | exact resolve eq41 eq7564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7758 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7731 X0
       have i₂ := eq7564 X0
       grind)
    | exact superpose eq7564 eq7731
    | exact resolve eq7731 eq7564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7731
  have eq7764 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7725 X0
       have i₂ := eq7564 X0
       grind)
    | exact superpose eq7564 eq7725
    | exact resolve eq7725 eq7564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7564 eq7725
  have eq8413 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq924 (σ X0) (σ X0)
       have i₂ := eq7764 X0
       grind)
    | exact superpose eq7764 eq924
    | exact resolve eq924 eq7764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8915 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq428
       have i₂ := eq7764 x
       grind)
    | exact superpose eq7764 eq428
    | exact resolve eq428 eq7764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq8919 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq8915
       grind)
    | exact superpose eq8915 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8915
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8915
       grind)
    | exact resolve eq13 eq8915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8915
  have eq8968 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq8919
  have eq8969 : y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq8968
  have eq58381 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq7467 X0 X1
       grind)
    | exact superpose eq7467 eq10
    | (have j1 := eq7467 X0 X1
       grind)
    | exact resolve eq10 eq7467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7467
  have eq58526 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58381 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq58381
    | (have j0 := eq58381 X0 X1
       grind)
    | exact resolve eq58381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58381
  have eq58611 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq58526 (σ X0) X1
       grind)
    | exact superpose eq58526 eq25
    | (have j1 := eq58526 (σ X0) X1
       grind)
    | exact resolve eq25 eq58526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq58526
  have eq58812 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58611 X0 X1
       have i₂ := eq7764 X0
       grind)
    | exact superpose eq7764 eq58611
    | (have j0 := eq58611 X0 X1
       grind)
    | exact resolve eq58611 eq7764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58611
  have eq1800287 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X1)
       have i₂ := eq58812 X1 (σ X0)
       grind)
    | exact superpose eq58812 eq34
    | (have j1 := eq58812 X1 (σ X0)
       grind)
    | exact resolve eq34 eq58812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq58812
  have eq1800779 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1800287 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1800287
    | (have j0 := eq1800287 X0 X1
       grind)
    | exact resolve eq1800287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800287
  have eq1801083 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1800779 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1800779
    | (have j0 := eq1800779 X0 X1
       grind)
    | exact resolve eq1800779 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800779
  have eq1801196 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1801083 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1801083
    | (have j0 := eq1801083 X0 X1
       grind)
    | exact resolve eq1801083 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801083
  have eq1856612 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (k X1 (τ X0)) = X1 ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1801196 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1801196
    | (have j0 := eq1801196 X1 (τ X0)
       grind)
    | exact resolve eq1801196 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801196
  have eq1857999 : ∀ X0 X1 : G, (σ X1) = (σ (τ (M.op X0 X0))) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1856612 X0 X1
       have i₂ := eq7758 X0
       grind)
    | exact superpose eq7758 eq1856612
    | (have j0 := eq1856612 X0 X1
       grind)
    | exact resolve eq1856612 eq7758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7758 eq1856612
  have eq1858172 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1857999 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1857999
    | (have j0 := eq1857999 X0 X1
       grind)
    | exact resolve eq1857999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857999
  have eq1902334 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1858172 X0 (τ X1)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq1858172
    | (have j0 := eq1858172 X1 (τ X0)
       grind)
    | exact resolve eq1858172 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1858172
  have eq1903180 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1902334 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1902334
    | (have j0 := eq1902334 X0 X1
       grind)
    | exact resolve eq1902334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902334
  have eq1903548 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1903180 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1903180
    | (have j0 := eq1903180 X0 X1
       grind)
    | exact resolve eq1903180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903180
  have eq1907284 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) ≠ (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1903548 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903548
  have eq1910141 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (τ X0) ≠ (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq1907284 X0 X1
       grind)
    | exact superpose eq1907284 eq11
    | (have j1 := eq1907284 X0 X1
       grind)
    | exact resolve eq11 eq1907284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907284
  have eq1910630 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1910141 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1910141
    | (have j0 := eq1910141 X0 X1
       grind)
    | exact resolve eq1910141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910141
  have eq1914087 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1910630 (σ X0) (σ X1)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq1910630
    | (have j0 := eq1910630 (σ X0) (σ X1)
       have j1 := eq37 X0 X1
       grind)
    | exact resolve eq1910630 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1910630
  have eq1914400 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1914087 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914087
  have eq1915299 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1914400 X0 X1
       have j1 := eq2226 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq1914400 X0 X1
       have r₂ := eq2226 (σ X0) (σ X1)
       grind)
    | exact resolve eq1914400 eq2226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226 eq1914400
  have eq1915432 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1915299 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1915299
    | (have j0 := eq1915299 X0 X1
       grind)
    | exact resolve eq1915299 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915299
  have eq1915473 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1915432 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1915432
    | (have j0 := eq1915432 X0 X1
       grind)
    | exact resolve eq1915432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915432
  have eq1915490 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1915473 X0 X1
       have i₂ := eq7764 X1
       grind)
    | exact superpose eq7764 eq1915473
    | (have j0 := eq1915473 X0 X1
       grind)
    | exact resolve eq1915473 eq7764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915473
  have eq2640219 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq1915490 y x
       grind)
    | (have r₁ := eq8969
       have r₂ := eq1915490 y x
       grind)
    | exact resolve eq8969 eq1915490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8969 eq1915490
  have eq2640320 : (M.op x x) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2640219
       grind)
    | exact superpose eq2640219 eq10
    | exact resolve eq10 eq2640219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640219
  have eq2641446 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2640320
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2640320
    | exact resolve eq2640320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640320
  have eq2641447 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2641446
  have eq2643659 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8413 x
       have i₂ := eq2641447
       grind)
    | exact superpose eq2641447 eq8413
    | exact resolve eq8413 eq2641447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8413 eq2641447
  have eq2645048 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2643659
  have eq2647178 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2645048
       grind)
    | exact superpose eq2645048 eq16
    | exact resolve eq16 eq2645048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2648453 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3592 (σ x) (σ y)
       have i₂ := eq2645048
       grind)
    | exact superpose eq2645048 eq3592
    | exact resolve eq3592 eq2645048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592 eq2645048
  have eq2648652 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2648453
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2648453
    | exact resolve eq2648453 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648453
  have eq2648693 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq2648652
       have i₂ := eq7764 x
       grind)
    | exact superpose eq7764 eq2648652
    | exact resolve eq2648652 eq7764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7764 eq2648652
  have eq2679645 : (M.op x x) = (τ (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2648693
       grind)
    | exact superpose eq2648693 eq10
    | exact resolve eq10 eq2648693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648693
  have eq2680775 : (σ y) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2679645
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2679645
    | exact resolve eq2679645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2679645
  have eq2687583 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq331 x y
       have i₂ := eq2680775
       grind)
    | exact superpose eq2680775 eq331
    | (have j0 := eq331 x y
       grind)
    | exact resolve eq331 eq2680775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq2680775
  have eq2688753 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq2687583
  have eq2688840 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2688753
       have r₂ := eq2647178
       grind)
    | exact resolve eq2688753 eq2647178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688753
  have eq2694300 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2647178
       have i₂ := eq2688840
       grind)
    | exact superpose eq2688840 eq2647178
    | exact resolve eq2647178 eq2688840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688840
  have eq2695381 : y = (M.op x x) := by grind
  clear eq2694300
  have eq2697774 : y = (M.op x y) := by
    first
    | (have i₁ := eq924 x x
       have i₂ := eq2695381
       grind)
    | exact superpose eq2695381 eq924
    | exact resolve eq924 eq2695381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924 eq2695381
  have eq2702263 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2647178
       have i₂ := eq2697774
       grind)
    | exact superpose eq2697774 eq2647178
    | exact resolve eq2647178 eq2697774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647178 eq2697774
  have eq2703329 : False := by grind
  exact eq2703329

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq380 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq388 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq14
    | exact resolve eq14 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq698 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  clear eq65
  have eq709 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq712 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq709 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq709 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq709 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq709 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq722 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq712
    | (have j0 := eq712 X0 X1
       grind)
    | exact resolve eq712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq872 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq388
    | exact resolve eq388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq388
    | exact resolve eq388 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq876 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq388
    | exact resolve eq388 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq388
  have eq8217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8217
    | exact resolve eq8217 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8217
  have eq8229 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8218
       have r₂ := eq28
       grind)
    | exact resolve eq8218 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8218
  have eq8231 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8229
    | exact resolve eq8229 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8229
  have eq8251 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq8270 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8231 eq872
    | exact resolve eq872 eq8231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8231
  have eq8271 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8270
    | exact resolve eq8270 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8270
  have eq8292 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8271
  have eq8550 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq8292
       grind)
    | exact superpose eq8292 eq87
    | exact resolve eq87 eq8292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq8292
  have eq8564 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8550
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8550
    | exact resolve eq8550 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8550
  have eq8787 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8564 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8564
  have eq8790 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8787
    | exact resolve eq8787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8787
  have eq8791 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8790
  have eq8803 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq8791
    | exact resolve eq8791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8791
  have eq8804 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8803
  have eq8848 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8804 eq872
    | exact resolve eq872 eq8804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8804
  have eq8849 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq8848
    | exact resolve eq8848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8848
  have eq8850 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8849
  have eq8852 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8850 eq28
    | exact resolve eq28 eq8850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8850
  have eq9862 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8251 eq100
    | exact resolve eq100 eq8251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8251
  have eq9870 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9862
  have eq9878 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9870
       have r₂ := eq8852
       grind)
    | exact resolve eq9870 eq8852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9870
  have eq10155 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq872 x x
       have i₂ := eq9878
       grind)
    | exact superpose eq9878 eq872
    | exact resolve eq872 eq9878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9878
  have eq10156 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10155
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10155
    | exact resolve eq10155 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10155
  have eq10165 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10156 eq216
    | exact resolve eq216 eq10156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10186 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10156 eq876
    | exact resolve eq876 eq10156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12219 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10186 eq10165
    | exact resolve eq10165 eq10186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10165 eq10186
  have eq12263 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12219
  have eq12266 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12263
    | exact resolve eq12263 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12263
  have eq12268 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12266 eq28
    | exact resolve eq28 eq12266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12296 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12266 eq10156
    | exact resolve eq10156 eq12266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10156
  have eq12299 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12296
  have eq13008 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12299 eq27
    | exact resolve eq27 eq12299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12299
  have eq15169 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq13008
  have eq15216 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12266 eq15169
    | exact resolve eq15169 eq12266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12266 eq15169
  have eq15230 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15216
  have eq16067 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15230 eq100
    | exact resolve eq100 eq15230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq15230
  have eq16081 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq16067
  have eq16092 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16081
       have r₂ := eq12268
       grind)
    | exact resolve eq16081 eq12268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12268 eq16081
  have eq17322 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq872 x x
       have i₂ := eq16092
       grind)
    | exact superpose eq16092 eq872
    | exact resolve eq872 eq16092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq16092
  have eq17325 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17322
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17322
    | exact resolve eq17322 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17322
  have eq17326 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17325
  have eq17328 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17326 eq21
    | exact resolve eq21 eq17326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17326
  have eq17464 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17328
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17328
    | exact resolve eq17328 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17328
  have eq17562 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17464 eq8852
    | (have r₁ := eq8852
       have r₂ := eq17464
       grind)
    | exact resolve eq8852 eq17464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8852
  have eq17590 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17562
  have eq17591 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17590
  have eq17656 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17591 eq216
    | exact resolve eq216 eq17591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq17678 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17591 eq876
    | exact resolve eq876 eq17591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq17591
  have eq21552 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17678 eq17656
    | exact resolve eq17656 eq17678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17656 eq17678
  have eq21608 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21552
  have eq21613 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq21608
    | exact resolve eq21608 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21608
  have eq21634 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21613 eq28
    | exact resolve eq28 eq21613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21613
  have eq21697 : x = (M.op x y) := by
    first
    | (have r₁ := eq21634
       have r₂ := eq17464
       grind)
    | exact resolve eq21634 eq17464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17464 eq21634
  have eq21701 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21697 eq21
    | exact resolve eq21 eq21697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21778 : x = (M.op x x) := by
    first
    | exact superpose eq21697 eq874
    | exact resolve eq874 eq21697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq21847 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21701
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21701
    | exact resolve eq21701 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21701
  have eq21856 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21847 eq27
    | exact resolve eq27 eq21847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq22025 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq21778
       grind)
    | exact superpose eq21778 eq47
    | exact resolve eq47 eq21778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq22047 : x = (k x x) := by grind
  have eq22117 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq21697 eq22025
    | exact resolve eq22025 eq21697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22025
  have eq22136 : y = (M.op x y) := by
    first
    | (have i₁ := eq22117
       have i₂ := eq21778
       grind)
    | exact superpose eq21778 eq22117
    | exact resolve eq22117 eq21778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21778 eq22117
  have eq22145 : y = (M.op x y) := by
    first
    | (have i₁ := eq22136
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22136
    | exact resolve eq22136 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22136
  have eq22151 : x = y := by
    first
    | exact superpose eq21697 eq22145
    | exact resolve eq22145 eq21697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21697 eq22145
  have eq22161 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq22151
       grind)
    | exact superpose eq22151 eq25
    | exact resolve eq25 eq22151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22151
  have eq22307 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22161
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22161
    | exact resolve eq22161 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22161
  have eq22370 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21847 eq22307
    | exact resolve eq22307 eq21847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22307
  have eq22624 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22370 eq21856
    | exact resolve eq21856 eq22370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21856 eq22370
  have eq22700 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq722 x x
       have i₂ := eq22047
       grind)
    | exact superpose eq22047 eq722
    | (have j0 := eq722 x x
       grind)
    | exact resolve eq722 eq22047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq22047
  have eq22701 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22700
  have eq22702 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22701
  have eq22717 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22702
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22702
    | exact resolve eq22702 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22702
  have eq22734 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21847 eq22717
    | exact resolve eq22717 eq21847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21847 eq22717
  have eq22816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22624 eq22734
    | exact resolve eq22734 eq22624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22624 eq22734
  have eq22817 : False := by grind
  exact eq22817

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_x_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq380 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq388 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq14
    | exact resolve eq14 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq698 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  clear eq65
  have eq709 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq712 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq709 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq709 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq709 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq709 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq722 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq712
    | (have j0 := eq712 X0 X1
       grind)
    | exact resolve eq712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq872 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq388
    | exact resolve eq388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq388
    | exact resolve eq388 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq876 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq388
    | exact resolve eq388 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq388
  have eq8157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8157
    | exact resolve eq8157 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8157
  have eq8169 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8158
       have r₂ := eq28
       grind)
    | exact resolve eq8158 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8158
  have eq8171 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8169
    | exact resolve eq8169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8169
  have eq8191 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq8210 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8171 eq872
    | exact resolve eq872 eq8171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8171
  have eq8211 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8210
    | exact resolve eq8210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8210
  have eq8232 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8211
  have eq8486 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq8232
       grind)
    | exact superpose eq8232 eq87
    | exact resolve eq87 eq8232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq8232
  have eq8500 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8486
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8486
    | exact resolve eq8486 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8486
  have eq8720 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8500 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8500
  have eq8723 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8720
    | exact resolve eq8720 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8720
  have eq8724 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8723
  have eq8736 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq8724
    | exact resolve eq8724 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8724
  have eq8737 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8736
  have eq8781 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8737 eq872
    | exact resolve eq872 eq8737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8737
  have eq8782 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq8781
    | exact resolve eq8781 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8781
  have eq8783 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8782
  have eq8785 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8783 eq28
    | exact resolve eq28 eq8783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8783
  have eq9786 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8191 eq100
    | exact resolve eq100 eq8191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8191
  have eq9794 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9786
  have eq9802 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9794
       have r₂ := eq8785
       grind)
    | exact resolve eq9794 eq8785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9794
  have eq10077 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq872 x x
       have i₂ := eq9802
       grind)
    | exact superpose eq9802 eq872
    | exact resolve eq872 eq9802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9802
  have eq10078 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10077
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10077
    | exact resolve eq10077 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10077
  have eq10087 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10078 eq216
    | exact resolve eq216 eq10078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10108 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10078 eq876
    | exact resolve eq876 eq10078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12053 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10108 eq10087
    | exact resolve eq10087 eq10108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10087 eq10108
  have eq12097 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12053
  have eq12099 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12097
    | exact resolve eq12097 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12097
  have eq12101 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12099 eq28
    | exact resolve eq28 eq12099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12129 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12099 eq10078
    | exact resolve eq10078 eq12099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10078
  have eq12132 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12129
  have eq12840 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12132 eq27
    | exact resolve eq27 eq12132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12132
  have eq14996 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12840
  have eq15043 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12099 eq14996
    | exact resolve eq14996 eq12099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12099 eq14996
  have eq15058 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15043
  have eq15893 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15058 eq100
    | exact resolve eq100 eq15058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq15058
  have eq15908 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq15893
  have eq15919 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15908
       have r₂ := eq12101
       grind)
    | exact resolve eq15908 eq12101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12101 eq15908
  have eq17408 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq872 x x
       have i₂ := eq15919
       grind)
    | exact superpose eq15919 eq872
    | exact resolve eq872 eq15919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq15919
  have eq17411 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17408
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17408
    | exact resolve eq17408 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17408
  have eq17412 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17411
  have eq17414 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17412 eq21
    | exact resolve eq21 eq17412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17412
  have eq17548 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17414
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17414
    | exact resolve eq17414 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17414
  have eq17912 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17548 eq8785
    | (have r₁ := eq8785
       have r₂ := eq17548
       grind)
    | exact resolve eq8785 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8785
  have eq17940 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17912
  have eq17941 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17940
  have eq18006 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17941 eq216
    | exact resolve eq216 eq17941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq18027 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17941 eq876
    | exact resolve eq876 eq17941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq17941
  have eq21407 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18027 eq18006
    | exact resolve eq18006 eq18027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18006 eq18027
  have eq21463 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21407
  have eq21467 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq21463
    | exact resolve eq21463 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21463
  have eq21507 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21467 eq28
    | exact resolve eq28 eq21467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21467
  have eq21571 : x = (M.op x y) := by
    first
    | (have r₁ := eq21507
       have r₂ := eq17548
       grind)
    | exact resolve eq21507 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17548 eq21507
  have eq21575 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21571 eq21
    | exact resolve eq21 eq21571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21655 : x = (M.op x x) := by
    first
    | exact superpose eq21571 eq874
    | exact resolve eq874 eq21571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq21723 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21575
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21575
    | exact resolve eq21575 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21575
  have eq21734 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21723 eq27
    | exact resolve eq27 eq21723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq21904 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq21655
       grind)
    | exact superpose eq21655 eq47
    | exact resolve eq47 eq21655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq21927 : x = (k x x) := by grind
  have eq21998 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq21571 eq21904
    | exact resolve eq21904 eq21571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21904
  have eq22018 : y = (M.op x y) := by
    first
    | (have i₁ := eq21998
       have i₂ := eq21655
       grind)
    | exact superpose eq21655 eq21998
    | exact resolve eq21998 eq21655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21655 eq21998
  have eq22028 : y = (M.op x y) := by
    first
    | (have i₁ := eq22018
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22018
    | exact resolve eq22018 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22018
  have eq22034 : x = y := by
    first
    | exact superpose eq21571 eq22028
    | exact resolve eq22028 eq21571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21571 eq22028
  have eq22046 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq22034
       grind)
    | exact superpose eq22034 eq25
    | exact resolve eq25 eq22034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22034
  have eq22194 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22046
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22046
    | exact resolve eq22046 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22046
  have eq22258 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21723 eq22194
    | exact resolve eq22194 eq21723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22194
  have eq22604 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22258 eq21734
    | exact resolve eq21734 eq22258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21734 eq22258
  have eq22672 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq722 x x
       have i₂ := eq21927
       grind)
    | exact superpose eq21927 eq722
    | (have j0 := eq722 x x
       grind)
    | exact resolve eq722 eq21927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq21927
  have eq22673 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22672
  have eq22674 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22673
  have eq22689 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22674
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22674
    | exact resolve eq22674 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22674
  have eq22706 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21723 eq22689
    | exact resolve eq22689 eq21723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21723 eq22689
  have eq22787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22604 eq22706
    | exact resolve eq22706 eq22604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22604 eq22706
  have eq22788 : False := by grind
  exact eq22788
