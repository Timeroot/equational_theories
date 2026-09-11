import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4294`: `x ◇ (x ◇ y) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_pxx_pxx_pxy_Equation4294 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4294 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4294.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X1 X2)) := by
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
  have eq179 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op x (M.op x y)) := by
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
  have eq180 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
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
  have eq185 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
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
  have eq194 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) X1)) := by
    intro X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq199 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | (have i₁ := eq196 x X1
       have i₂ := eq188 x X1
       grind)
    | (have i₁ := eq196 x y
       have i₂ := eq188 x X1
       grind)
    | exact superpose eq188 eq196
    | exact resolve eq196 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq200 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq195 x
       have i₂ := eq188 sF2 x
       grind)
    | exact superpose eq188 eq195
    | (have j1 := eq188 (σ x) (σ y)
       grind)
    | exact resolve eq195 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq213 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq188 X0 (M.op X0 x)
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq188
    | exact resolve eq188 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq188
  have eq224 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq200 eq213
    | exact resolve eq213 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq288 : (M.op x (M.op x y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (M.op x y))) := by
    first
    | exact superpose eq199 eq185
    | exact resolve eq185 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq298 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq200 eq288
    | exact resolve eq288 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq288
  have eq444 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq501 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq528 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq444 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq444
    | exact resolve eq444 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq1176 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq224 eq28
    | (have j0 := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq224 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq28 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1180 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq1176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1233 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1239 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1180 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq1180
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1381 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1180 eq501
    | exact resolve eq501 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1390 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq2502 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1233
       grind)
    | exact superpose eq1233 eq41
    | exact resolve eq41 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq2503 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2502
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2502
    | exact resolve eq2502 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502
  have eq2505 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2503
    | exact resolve eq2503 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq18522 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1180 (M.op sF2 sF4)
       have i₂ := eq1390 (M.op sF2 sF4)
       grind)
    | exact superpose eq1390 eq1180
    | (have j1 := eq1390 X0
       grind)
    | exact resolve eq1180 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq18627 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18522 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq18522 X0
       have r₂ := eq13 X0 (k X0 X0)
       grind)
    | (have r₁ := eq18522 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq18522 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq18522 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18522
  have eq18740 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq194 X0 X0
       have i₂ := eq18627 X0
       grind)
    | exact superpose eq18627 eq194
    | exact resolve eq194 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18753 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1381 X0
       have i₂ := eq18627 (σ X0)
       grind)
    | exact superpose eq18627 eq1381
    | exact resolve eq1381 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq18772 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq18753 X0
       have i₂ := eq501 X0 (σ X0)
       grind)
    | exact superpose eq501 eq18753
    | exact resolve eq18753 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18753
  have eq18802 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq18772 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq18772
    | exact resolve eq18772 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18772
  have eq19155 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18740 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq18740
    | exact resolve eq18740 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19156 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18740 (τ X0)
       have i₂ := eq528 X0 X0
       grind)
    | exact superpose eq528 eq18740
    | exact resolve eq18740 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22497 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq298 eq19155
    | exact resolve eq19155 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22593 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq22497
       have i₂ := eq1180 (σ (M.op sF2 sF4))
       grind)
    | exact superpose eq1180 eq22497
    | exact resolve eq22497 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq22497
  have eq25856 : (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq22593 eq501
    | exact resolve eq501 eq22593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq22593
  have eq25863 : (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq18802 eq25856
    | exact resolve eq25856 eq18802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18802 eq25856
  have eq25865 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq298 eq25863
    | exact resolve eq25863 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq25863
  have eq25879 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq25865 eq14
    | exact resolve eq14 eq25865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25865
  have eq33618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2505 eq1239
    | exact resolve eq1239 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq2505
  have eq33625 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq33618
       have r₂ := eq27
       grind)
    | exact resolve eq33618 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33618
  have eq33631 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33625
       have i₂ := eq18627 sF3
       grind)
    | exact superpose eq18627 eq33625
    | exact resolve eq33625 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33625
  have eq33635 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33631
       have i₂ := eq18627 sF2
       grind)
    | exact superpose eq18627 eq33631
    | exact resolve eq33631 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33631
  have eq33639 : y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33635
       have i₂ := eq18627 y
       grind)
    | exact superpose eq18627 eq33635
    | exact resolve eq33635 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33635
  have eq33641 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33639
       have i₂ := eq18627 x
       grind)
    | exact superpose eq18627 eq33639
    | exact resolve eq33639 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33639
  have eq33648 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq33641 eq153
    | exact resolve eq153 eq33641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq33641
  have eq33676 : y = (k y y) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq33648
    | exact resolve eq33648 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33648
  have eq33677 : (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by grind
  clear eq33676
  have eq33697 : (τ (σ y)) = (k x x) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq33677 eq98
    | exact resolve eq98 eq33677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq33677
  have eq33722 : y = (k x x) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq33697
    | exact resolve eq33697 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq33697
  have eq33723 : y = (k y y) ∨ y = (k x x) := by grind
  clear eq33722
  have eq33737 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq33723
       grind)
    | exact superpose eq33723 eq41
    | exact resolve eq41 eq33723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33746 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq18740 y
       have i₂ := eq33723
       grind)
    | exact superpose eq33723 eq18740
    | exact resolve eq18740 eq33723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33747 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19155 y
       have i₂ := eq33723
       grind)
    | exact superpose eq33723 eq19155
    | exact resolve eq19155 eq33723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33748 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19156 y
       have i₂ := eq33723
       grind)
    | exact superpose eq33723 eq19156
    | exact resolve eq19156 eq33723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19156
  have eq33757 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33748
       have i₂ := eq18627 (τ y)
       grind)
    | exact superpose eq18627 eq33748
    | exact resolve eq33748 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33748
  have eq33758 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33747
       have i₂ := eq18627 (σ y)
       grind)
    | exact superpose eq18627 eq33747
    | exact resolve eq33747 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33747
  have eq33759 : (k y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33746
       have i₂ := eq18627 y
       grind)
    | exact superpose eq18627 eq33746
    | exact resolve eq33746 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33746
  have eq33764 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33737
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33737
    | exact resolve eq33737 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33737
  have eq33770 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (k y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33757
       have i₂ := eq528 y y
       grind)
    | exact superpose eq528 eq33757
    | exact resolve eq33757 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq33757
  have eq33771 : (σ (k y y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33758
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq33758
    | exact resolve eq33758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33758
  have eq33772 : y = (k x x) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33723 eq33759
    | exact resolve eq33759 eq33723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33759
  have eq33777 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ y) ∨ y = (k x x) := by
    first
    | exact superpose eq33723 eq33770
    | exact resolve eq33770 eq33723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33723 eq33770
  have eq33778 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33771
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq33771
    | exact resolve eq33771 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq33771
  have eq33782 : y = (k x x) ∨ y = (τ y) := by
    first
    | exact superpose eq33772 eq33777
    | exact resolve eq33777 eq33772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33777
  have eq33783 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33778
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33778
    | exact resolve eq33778 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33778
  have eq33787 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | exact superpose eq33764 eq33783
    | exact resolve eq33783 eq33764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33764 eq33783
  have eq33804 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq18740 x
       have i₂ := eq33782
       grind)
    | exact superpose eq33782 eq18740
    | exact resolve eq18740 eq33782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33805 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq19155 x
       have i₂ := eq33782
       grind)
    | exact superpose eq33782 eq19155
    | exact resolve eq19155 eq33782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33782
  have eq33810 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq33805
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33805
    | exact resolve eq33805 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33805
  have eq33811 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq33804
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33804
    | exact resolve eq33804 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33804
  have eq33821 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq33810
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33810
    | exact resolve eq33810 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33810
  have eq33827 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | exact superpose eq26 eq33821
    | exact resolve eq33821 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33821
  have eq33830 : y = (τ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33811 eq33827
    | exact resolve eq33827 eq33811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33827
  have eq33835 : y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq33830
       grind)
    | exact superpose eq33830 eq14
    | exact resolve eq14 eq33830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33830
  have eq33891 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq33835
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33835
    | exact resolve eq33835 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33835
  have eq33906 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq33891 eq27
    | exact resolve eq27 eq33891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33891
  have eq34434 : (M.op x y) = (σ (M.op x y)) ∨ y = (τ y) := by
    first
    | exact superpose eq33811 eq25879
    | exact resolve eq25879 eq33811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33811
  have eq34452 : y = (τ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq34434
    | exact resolve eq34434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34434
  have eq34633 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq34452
       grind)
    | exact superpose eq34452 eq14
    | exact resolve eq14 eq34452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34452
  have eq34689 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq34633
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34633
    | exact resolve eq34633 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34633
  have eq34696 : y = (σ y) := by
    first
    | (have r₁ := eq34689
       have r₂ := eq33906
       grind)
    | exact resolve eq34689 eq33906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33906 eq34689
  have eq34712 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq34696
       grind)
    | exact superpose eq34696 eq18
    | exact resolve eq18 eq34696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34713 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq34696
       grind)
    | exact superpose eq34696 eq24
    | exact resolve eq24 eq34696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37884 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18740 x
       have i₂ := eq33772
       grind)
    | exact superpose eq33772 eq18740
    | exact resolve eq18740 eq33772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18740
  have eq37885 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19155 x
       have i₂ := eq33772
       grind)
    | exact superpose eq33772 eq19155
    | exact resolve eq19155 eq33772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19155 eq33772
  have eq37892 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37885
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37885
    | exact resolve eq37885 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37885
  have eq37893 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37884
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37884
    | exact resolve eq37884 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq37884
  have eq37911 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37892
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37892
    | exact resolve eq37892 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37892
  have eq37912 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37893
       have i₂ := eq34696
       grind)
    | exact superpose eq34696 eq37893
    | exact resolve eq37893 eq34696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37893
  have eq37930 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq37911
    | exact resolve eq37911 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37911
  have eq37945 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37930
       have i₂ := eq34696
       grind)
    | exact superpose eq34696 eq37930
    | exact resolve eq37930 eq34696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37930
  have eq37954 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37912 eq37945
    | exact resolve eq37945 eq37912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37912 eq37945
  have eq37970 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37954 eq224
    | exact resolve eq224 eq37954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38058 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37954 eq194
    | exact resolve eq194 eq37954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37954
  have eq38059 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq38058
    | exact resolve eq38058 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38058
  have eq38325 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq38059
  have eq38684 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37970 eq34712
    | exact resolve eq34712 eq37970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37970
  have eq38691 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq38684
       have r₂ := eq38325
       grind)
    | exact resolve eq38684 eq38325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38325 eq38684
  have eq38712 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq38691 eq27
    | exact resolve eq27 eq38691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38714 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq38691 eq199
    | exact resolve eq199 eq38691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq38715 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq38691 eq224
    | exact resolve eq224 eq38691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq38792 : (M.op (σ x) (M.op x y)) = (σ (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq38691 eq25879
    | exact resolve eq25879 eq38691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25879
  have eq38850 : (M.op x (M.op x y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq38715 eq38714
    | exact resolve eq38714 eq38715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38714
  have eq38920 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op (σ x) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq38850 eq184
    | exact resolve eq184 eq38850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq38850
  have eq38926 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq38715 eq38920
    | exact resolve eq38920 eq38715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38715 eq38920
  have eq39994 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (σ x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq38926 X0 X0
       have i₂ := eq18627 X0
       grind)
    | exact superpose eq18627 eq38926
    | exact resolve eq38926 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18627 eq38926
  have eq40590 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq33787 eq194
    | exact resolve eq194 eq33787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq33787
  have eq40593 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq26 eq40590
    | exact resolve eq40590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq40590
  have eq40677 : (M.op x y) = (σ y) ∨ y = (k x x) := by
    first
    | exact superpose eq38691 eq40593
    | exact resolve eq40593 eq38691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38691 eq40593
  have eq40739 : (σ y) = (k x x) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq40677
       have i₂ := eq34696
       grind)
    | exact superpose eq34696 eq40677
    | exact resolve eq40677 eq34696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34696 eq40677
  have eq40979 : (M.op (σ x) (M.op x y)) = (M.op x (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq39994 x
       have i₂ := eq40739
       grind)
    | exact superpose eq40739 eq39994
    | exact resolve eq39994 eq40739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39994 eq40739
  have eq40980 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq34712 eq40979
    | exact resolve eq40979 eq34712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34712 eq40979
  have eq41136 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq40980 eq38792
    | exact resolve eq38792 eq40980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38792 eq40980
  have eq41154 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq41136
    | exact resolve eq41136 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41136
  have eq41159 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq41154
       have r₂ := eq38712
       grind)
    | exact resolve eq41154 eq38712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41154
  have eq41355 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41159 eq34713
    | exact resolve eq34713 eq41159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34713 eq41159
  have eq41618 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41355 eq20
    | exact resolve eq20 eq41355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq41355
  have eq41774 : False := by grind
  exact eq41774

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation4301 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
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
  clear eq23
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
  have eq47 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X0 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq14 X0 (M.op X0 X1) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 x X3
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq14 X0 X0 x
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X2 (M.op X1 X3)
       have i₂ := eq14 X1 X3 X0
       grind)
    | (have i₁ := eq14 X2 X1 (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq14 X0 X1 (M.op X0 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq79
    | exact resolve eq79 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq100 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
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
  have eq216 : (M.op x (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op x y))) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq216 eq51
    | exact resolve eq51 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq216
  have eq480 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq439 X0
       have i₂ := eq47 sF0
       grind)
    | exact superpose eq47 eq439
    | exact resolve eq439 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq1225 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0 X1 x
       have i₂ := eq47 (M.op X0 x)
       grind)
    | exact superpose eq47 eq55
    | exact resolve eq55 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq55
  have eq1342 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1225 X0 (M.op X0 x)
       have i₂ := eq1225 X0 x
       grind)
    | (have i₁ := eq1225 x (M.op x y)
       have i₂ := eq1225 X0 x
       grind)
    | exact superpose eq1225 eq1225
    | exact resolve eq1225 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq1225
    | (have j0 := eq1225 (σ x) (σ y)
       grind)
    | exact resolve eq1225 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1371 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1225 X1 x
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq1225 X0 X0
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq1225
    | exact resolve eq1225 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1473 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 X2) (M.op x (M.op x y))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq56 X0 x X2 X3
       have i₂ := eq1225 X0 x
       grind)
    | (have i₁ := eq56 x y X2 X3
       have i₂ := eq1225 X0 x
       grind)
    | exact superpose eq1225 eq56
    | exact resolve eq56 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1474 : ∀ X0 X2 : G, (M.op x (M.op x y)) = (M.op (M.op X0 X2) (M.op x (M.op x y))) := by
    intro X0 X2
    first
    | (have i₁ := eq1473 X0 X2 x
       have i₂ := eq1225 X2 x
       grind)
    | (have i₁ := eq1473 X0 x y
       have i₂ := eq1225 X0 x
       grind)
    | exact superpose eq1225 eq1473
    | exact resolve eq1473 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1504 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) (M.op x (M.op x y))) := by grind
  clear eq1474
  have eq2091 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2092 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2091 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq7214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq7215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq7214
    | exact resolve eq7214 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7214
  have eq7226 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq7215
       have r₂ := eq28
       grind)
    | exact resolve eq7215 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7215
  have eq7228 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq7226
    | exact resolve eq7226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7226
  have eq7232 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq7228
  have eq7288 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq7232 eq66
    | exact resolve eq66 eq7232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq7232
  have eq7307 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq7288
    | exact resolve eq7288 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7288
  have eq8068 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq7307
       grind)
    | exact superpose eq7307 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq7307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7307
  have eq8069 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8068
  have eq8071 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8069
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8069
    | exact resolve eq8069 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8069
  have eq8072 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8071
  have eq8085 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq8090 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 x x X1 X0
       have i₂ := eq8072
       grind)
    | exact superpose eq8072 eq50
    | exact resolve eq50 eq8072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq8099 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1371 x x
       have i₂ := eq8072
       grind)
    | exact superpose eq8072 eq1371
    | exact resolve eq1371 eq8072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8072
  have eq8101 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8099
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8099
    | exact resolve eq8099 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8099
  have eq8110 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq8090 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8090
    | (have j0 := eq8090 X0 X1
       grind)
    | exact resolve eq8090 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8090
  have eq8122 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq8110 x X1
       have i₂ := eq1371 x X1
       grind)
    | exact superpose eq1371 eq8110
    | exact resolve eq8110 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8110
  have eq8128 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq8085
       grind)
    | exact superpose eq8085 eq45
    | exact resolve eq45 eq8085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq8085
  have eq8144 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8128
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8128
    | exact resolve eq8128 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8128
  have eq8152 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8101 eq1504
    | exact resolve eq1504 eq8101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8101
  have eq8211 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8144 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq8144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8144
  have eq8212 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8211
  have eq8216 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8212
    | exact resolve eq8212 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8212
  have eq8217 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8216
  have eq8294 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8152 eq125
    | exact resolve eq125 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq8152
  have eq8310 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq8294
    | exact resolve eq8294 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8294
  have eq8329 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8217 eq1371
    | exact resolve eq1371 eq8217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8217
  have eq8331 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq8329
    | exact resolve eq8329 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8329
  have eq8374 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8310 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq8310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8310
  have eq8375 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8374
  have eq8474 : (M.op x (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8375 eq1225
    | exact resolve eq1225 eq8375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8851 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8122 eq8331
    | exact resolve eq8331 eq8122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8122 eq8331
  have eq8905 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8851
  have eq9645 : (σ (M.op x y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8474 eq8375
    | exact resolve eq8375 eq8474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8375 eq8474
  have eq9664 : (σ (M.op x y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9645
  have eq9717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9664 eq8905
    | exact resolve eq8905 eq9664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8905 eq9664
  have eq9739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9717
  have eq9775 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9739
       have r₂ := eq28
       grind)
    | exact resolve eq9739 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9739
  have eq9788 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9775 eq1363
    | exact resolve eq1363 eq9775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq9803 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq9788
    | exact resolve eq9788 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9788
  have eq9824 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9803 eq1504
    | exact resolve eq1504 eq9803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9803
  have eq9995 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9775 eq9824
    | exact resolve eq9824 eq9775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9775 eq9824
  have eq10006 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9995
  have eq10083 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10006 eq115
    | exact resolve eq115 eq10006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq10006
  have eq10101 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq10083
    | exact resolve eq10083 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10083
  have eq10113 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq10101
       grind)
    | exact superpose eq10101 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq10101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10101
  have eq10114 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq10113
  have eq10125 : (M.op x (M.op x y)) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq480 y
       have i₂ := eq10114
       grind)
    | exact superpose eq10114 eq480
    | exact resolve eq480 eq10114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq11650 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10114
       have i₂ := eq10125
       grind)
    | exact superpose eq10125 eq10114
    | exact resolve eq10114 eq10125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10114 eq10125
  have eq11673 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq11650
  have eq11754 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11673 eq1225
    | exact resolve eq1225 eq11673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq11673
  have eq11797 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11754
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11754
    | exact resolve eq11754 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11754
  have eq11798 : y = (M.op x y) := by grind
  clear eq11797
  have eq11819 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq11798 eq21
    | exact resolve eq21 eq11798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq11872 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11798 eq1342
    | exact resolve eq1342 eq11798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq11875 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11798 eq1504
    | exact resolve eq1504 eq11798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq11883 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq11875
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11875
    | exact resolve eq11875 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11875
  have eq11886 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq11872 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11872
    | (have j0 := eq11872 X0
       grind)
    | exact resolve eq11872 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11872
  have eq11938 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11819
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11819
    | exact resolve eq11819 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11819
  have eq11941 : y = (k y y) := by
    first
    | exact superpose eq11798 eq11883
    | exact resolve eq11883 eq11798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11883
  have eq11944 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq11798 eq11886
    | exact resolve eq11886 eq11798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11886
  have eq11956 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq11938 eq27
    | exact resolve eq27 eq11938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq12093 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2092 y
       have i₂ := eq11941
       grind)
    | exact superpose eq11941 eq2092
    | (have j0 := eq2092 y
       grind)
    | exact resolve eq2092 eq11941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092 eq11941
  have eq12096 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq12093
  have eq12098 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12096
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12096
    | exact resolve eq12096 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12096
  have eq12106 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11938 eq12098
    | exact resolve eq12098 eq11938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11938 eq12098
  have eq12425 : (M.op x (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12106 eq1371
    | exact resolve eq1371 eq12106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq12427 : (σ (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq12106 eq12425
    | exact resolve eq12425 eq12106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12106 eq12425
  have eq12439 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq11798 eq12427
    | exact resolve eq12427 eq11798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12427
  have eq12450 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq12439
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12439
    | exact resolve eq12439 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq12439
  have eq12460 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq11798 eq12450
    | exact resolve eq12450 eq11798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11798 eq12450
  have eq12531 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq12460 eq11956
    | exact resolve eq11956 eq12460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11956
  have eq12534 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12531
       have i₂ := eq11944 sF2
       grind)
    | exact superpose eq11944 eq12531
    | exact resolve eq12531 eq11944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11944 eq12531
  have eq12716 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq12534 eq28
    | exact resolve eq28 eq12534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12534
  have eq12763 : False := by grind
  exact eq12763

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_pxx_pxx_pxy_Equation4301 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
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
  have eq175 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op x (M.op x y)) := by
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
  have eq176 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
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
  have eq188 : (M.op x (M.op x y)) = (M.op y (M.op x y)) := by
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
  have eq189 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op x X1) (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op x X1)
       have i₂ := eq16 x X1 X0
       grind)
    | (have i₁ := eq175 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x X1) (M.op x (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq189 x X1
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq189
    | exact resolve eq189 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq200 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x (σ x)) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq176 (M.op x sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq176
    | exact resolve eq176 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq210 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq198 eq203
    | exact resolve eq203 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq203
  have eq214 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq200 eq16
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq216 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq176 eq214
    | exact resolve eq214 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq225 : (M.op y (M.op x y)) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq176 eq181
    | exact resolve eq181 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq181
  have eq240 : (M.op x (M.op x y)) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq188 eq225
    | exact resolve eq225 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq225
  have eq246 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq212 eq240
    | exact resolve eq240 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq240
  have eq432 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ y) X1)) := by
    intro X1
    first
    | exact superpose eq216 eq16
    | exact resolve eq16 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ y) X1) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq216 eq16
    | exact resolve eq16 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | exact superpose eq216 eq434
    | exact resolve eq434 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq434
  have eq491 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq432 eq16
    | exact resolve eq16 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq436 eq491
    | exact resolve eq491 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq491
  have eq574 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq432 eq504
    | exact resolve eq504 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq668 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq574 eq187
    | exact resolve eq187 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq687 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq574 eq28
    | (have j0 := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq574 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq28 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq688 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq738 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq688 X0
       grind)
    | exact superpose eq688 eq11
    | exact resolve eq11 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : ∀ X0 X1 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) ≠ X1 ∨ (k X0 X1) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq688 X0
       grind)
    | exact superpose eq688 eq13
    | (have r₁ := eq13 X0 (k X0 (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq688 X0
       grind)
    | exact resolve eq13 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq903 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq921 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq917 X0
       have j1 := eq910 X0 X0
       grind)
    | (have r₁ := eq917 X0
       have r₂ := eq910 X0 (k X0 X0)
       grind)
    | (have r₁ := eq917 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq910 (M.op (σ x) (M.op (σ x) (σ y))) (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq917 x
       have r₂ := eq910 x x
       grind)
    | exact resolve eq917 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq917
  have eq925 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq688 (M.op sF2 sF4)
       have i₂ := eq921 (M.op sF2 sF4)
       grind)
    | exact superpose eq921 eq688
    | exact resolve eq688 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq504 X0 X0
       have i₂ := eq925 X0
       grind)
    | exact superpose eq925 eq504
    | exact resolve eq504 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq947 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq947
    | exact resolve eq947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq1167 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq1201 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1097 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1097
    | exact resolve eq1097 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1214 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (k (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1097 (σ X0) X0
       have i₂ := eq921 (σ X0)
       grind)
    | exact superpose eq921 eq1097
    | exact resolve eq1097 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq1097
  have eq1236 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1214 X0
       have i₂ := eq1167 X0 (M.op sF2 sF4)
       grind)
    | exact superpose eq1167 eq1214
    | exact resolve eq1214 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1241 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1236 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1236
    | exact resolve eq1236 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1360 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq947 (τ X0)
       have i₂ := eq1201 X0 X0
       grind)
    | exact superpose eq1201 eq947
    | exact resolve eq947 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8159 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq668 eq974
    | exact resolve eq974 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8229 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq8159
       have i₂ := eq688 (σ (M.op sF2 sF4))
       grind)
    | exact superpose eq688 eq8159
    | exact resolve eq8159 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq8159
  have eq9215 : (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq8229 eq1167
    | exact resolve eq1167 eq8229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq8229
  have eq9219 : (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1241 eq9215
    | exact resolve eq9215 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241 eq9215
  have eq9222 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq668 eq9219
    | exact resolve eq9219 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq9219
  have eq9241 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq9222 eq14
    | exact resolve eq14 eq9222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9222
  have eq9268 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq738
       grind)
    | exact superpose eq738 eq41
    | exact resolve eq41 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq9269 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9268
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9268
    | exact resolve eq9268 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9268
  have eq9271 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq9269
    | exact resolve eq9269 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9269
  have eq9273 : y = (k y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9271
       have i₂ := eq925 y
       grind)
    | exact superpose eq925 eq9271
    | exact resolve eq9271 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9271
  have eq9275 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq9273
       have i₂ := eq925 x
       grind)
    | exact superpose eq925 eq9273
    | exact resolve eq9273 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9273
  have eq40183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq9275 eq751
    | exact resolve eq751 eq9275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq9275
  have eq40192 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq40183
       have r₂ := eq27
       grind)
    | exact resolve eq40183 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40183
  have eq40199 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40192
       have i₂ := eq925 sF3
       grind)
    | exact superpose eq925 eq40192
    | exact resolve eq40192 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40192
  have eq40201 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40199
       have i₂ := eq925 sF2
       grind)
    | exact superpose eq925 eq40199
    | exact resolve eq40199 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40199
  have eq40209 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq40201 eq153
    | exact resolve eq153 eq40201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq40201
  have eq40239 : y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq40209
    | exact resolve eq40209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40209
  have eq40240 : (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by grind
  clear eq40239
  have eq40259 : (τ (σ y)) = (k x x) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq40240 eq98
    | exact resolve eq98 eq40240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq40240
  have eq40285 : y = (k x x) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq40259
    | exact resolve eq40259 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq40259
  have eq40286 : y = (k y y) ∨ y = (k x x) := by grind
  clear eq40285
  have eq40300 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq40286
       grind)
    | exact superpose eq40286 eq41
    | exact resolve eq41 eq40286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40305 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq947 y
       have i₂ := eq40286
       grind)
    | exact superpose eq40286 eq947
    | exact resolve eq947 eq40286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40308 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq974 y
       have i₂ := eq40286
       grind)
    | exact superpose eq40286 eq974
    | exact resolve eq974 eq40286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40309 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1360 y
       have i₂ := eq40286
       grind)
    | exact superpose eq40286 eq1360
    | exact resolve eq1360 eq40286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq40324 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40309
       have i₂ := eq925 (τ y)
       grind)
    | exact superpose eq925 eq40309
    | exact resolve eq40309 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40309
  have eq40325 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40308
       have i₂ := eq925 (σ y)
       grind)
    | exact superpose eq925 eq40308
    | exact resolve eq40308 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40308
  have eq40326 : (k y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40305
       have i₂ := eq925 y
       grind)
    | exact superpose eq925 eq40305
    | exact resolve eq40305 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40305
  have eq40329 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40300
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40300
    | exact resolve eq40300 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40300
  have eq40336 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (k y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40324
       have i₂ := eq1201 y y
       grind)
    | exact superpose eq1201 eq40324
    | exact resolve eq40324 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq40324
  have eq40337 : (σ (k y y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40325
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq40325
    | exact resolve eq40325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40325
  have eq40338 : y = (k x x) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq40286 eq40326
    | exact resolve eq40326 eq40286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40326
  have eq40341 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ y) ∨ y = (k x x) := by
    first
    | exact superpose eq40286 eq40336
    | exact resolve eq40336 eq40286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40286 eq40336
  have eq40342 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40337
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq40337
    | exact resolve eq40337 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq40337
  have eq40345 : y = (k x x) ∨ y = (τ y) := by
    first
    | exact superpose eq40338 eq40341
    | exact resolve eq40341 eq40338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40341
  have eq40346 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40342
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40342
    | exact resolve eq40342 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40342
  have eq40349 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | exact superpose eq40329 eq40346
    | exact resolve eq40346 eq40329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40329 eq40346
  have eq40362 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq947 x
       have i₂ := eq40345
       grind)
    | exact superpose eq40345 eq947
    | exact resolve eq947 eq40345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40365 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq974 x
       have i₂ := eq40345
       grind)
    | exact superpose eq40345 eq974
    | exact resolve eq974 eq40345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40345
  have eq40376 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq40365
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40365
    | exact resolve eq40365 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40365
  have eq40377 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq40362
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40362
    | exact resolve eq40362 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40362
  have eq40388 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq40376
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40376
    | exact resolve eq40376 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40376
  have eq40393 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | exact superpose eq26 eq40388
    | exact resolve eq40388 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40388
  have eq40394 : y = (τ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40377 eq40393
    | exact resolve eq40393 eq40377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40393
  have eq40395 : y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq40394
       grind)
    | exact superpose eq40394 eq14
    | exact resolve eq14 eq40394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40394
  have eq40449 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq40395
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40395
    | exact resolve eq40395 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40395
  have eq40455 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq40449 eq27
    | exact resolve eq27 eq40449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40449
  have eq42159 : (M.op x y) = (σ (M.op x y)) ∨ y = (τ y) := by
    first
    | exact superpose eq40377 eq9241
    | exact resolve eq9241 eq40377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40377
  have eq42228 : y = (τ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq42159
    | exact resolve eq42159 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42159
  have eq42503 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq42228
       grind)
    | exact superpose eq42228 eq14
    | exact resolve eq14 eq42228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42228
  have eq42557 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq42503
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42503
    | exact resolve eq42503 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42503
  have eq42561 : y = (σ y) := by
    first
    | (have r₁ := eq42557
       have r₂ := eq40455
       grind)
    | exact resolve eq42557 eq40455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40455 eq42557
  have eq42564 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq42561
       grind)
    | exact superpose eq42561 eq18
    | exact resolve eq18 eq42561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42565 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq42561
       grind)
    | exact superpose eq42561 eq24
    | exact resolve eq24 eq42561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45576 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq947 x
       have i₂ := eq40338
       grind)
    | exact superpose eq40338 eq947
    | exact resolve eq947 eq40338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq45579 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq974 x
       have i₂ := eq40338
       grind)
    | exact superpose eq40338 eq974
    | exact resolve eq974 eq40338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq40338
  have eq45595 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq45579
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45579
    | exact resolve eq45579 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq45579
  have eq45598 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq45576
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45576
    | exact resolve eq45576 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq45576
  have eq45614 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq45595
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45595
    | exact resolve eq45595 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45595
  have eq45617 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq45598
       have i₂ := eq42561
       grind)
    | exact superpose eq42561 eq45598
    | exact resolve eq45598 eq42561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45598
  have eq45632 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq45614
    | exact resolve eq45614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45614
  have eq45644 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq45632
       have i₂ := eq42561
       grind)
    | exact superpose eq42561 eq45632
    | exact resolve eq45632 eq42561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45632
  have eq45650 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45617 eq45644
    | exact resolve eq45644 eq45617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45617 eq45644
  have eq45668 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq45650 eq574
    | exact resolve eq574 eq45650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45792 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45650 eq504
    | exact resolve eq504 eq45650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq45650
  have eq45796 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq45792
    | exact resolve eq45792 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq45792
  have eq46187 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq45796
  have eq48311 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45668 eq42564
    | exact resolve eq42564 eq45668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45668
  have eq48350 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq48311
       have r₂ := eq46187
       grind)
    | exact resolve eq48311 eq46187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46187 eq48311
  have eq48391 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq48350 eq27
    | exact resolve eq27 eq48350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq48395 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op (σ x) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq48350 eq210
    | exact resolve eq210 eq48350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq48405 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq48350 eq574
    | exact resolve eq574 eq48350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq48490 : (M.op (σ x) (M.op x y)) = (σ (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq48350 eq9241
    | exact resolve eq9241 eq48350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9241 eq48350
  have eq48565 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq48405 eq48395
    | exact resolve eq48395 eq48405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48395 eq48405
  have eq50032 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48565 X0 X0
       have i₂ := eq925 X0
       grind)
    | exact superpose eq925 eq48565
    | exact resolve eq48565 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq48565
  have eq51308 : (σ y) = (M.op x (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq40349 eq246
    | exact resolve eq246 eq40349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq40349
  have eq51564 : (M.op x y) = (σ y) ∨ y = (k x x) := by
    first
    | exact superpose eq42564 eq51308
    | exact resolve eq51308 eq42564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51308
  have eq51653 : (σ y) = (k x x) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq51564
       have i₂ := eq42561
       grind)
    | exact superpose eq42561 eq51564
    | exact resolve eq51564 eq42561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42561 eq51564
  have eq51856 : (M.op x (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq50032 x
       have i₂ := eq51653
       grind)
    | exact superpose eq51653 eq50032
    | exact resolve eq50032 eq51653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50032 eq51653
  have eq51868 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq42564 eq51856
    | exact resolve eq51856 eq42564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42564 eq51856
  have eq52071 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq51868 eq48490
    | exact resolve eq48490 eq51868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48490 eq51868
  have eq52123 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq52071
    | exact resolve eq52071 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52071
  have eq52134 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq52123
       have r₂ := eq48391
       grind)
    | exact resolve eq52123 eq48391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52123
  have eq52214 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq52134 eq42565
    | exact resolve eq42565 eq52134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42565 eq52134
  have eq52473 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq52214 eq20
    | exact resolve eq20 eq52214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq52214
  have eq52629 : False := by grind
  exact eq52629

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pxy_Equation4301 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op x (M.op x y)) := by
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
  have eq176 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X0 X2) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | (have i₁ := eq16 X0 (M.op X0 X1) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (M.op x (M.op x y)) = (M.op y (M.op x y)) := by
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
  have eq191 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op x X1) (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op x X1)
       have i₂ := eq16 x X1 X0
       grind)
    | (have i₁ := eq175 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x X1) (M.op x (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq191 x X1
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq191
    | exact resolve eq191 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq202 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x (σ x)) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq176 (M.op x sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq176
    | exact resolve eq176 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq214 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq200 eq205
    | exact resolve eq205 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq205
  have eq216 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq202 eq16
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq176 eq216
    | exact resolve eq216 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq216
  have eq225 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op x (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq181 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | (have i₁ := eq181 (M.op x X1)
       have i₂ := eq16 x X1 x
       grind)
    | exact superpose eq16 eq181
    | exact resolve eq181 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq243 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq190 eq225
    | exact resolve eq225 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq225
  have eq249 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq214 eq243
    | exact resolve eq243 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq254 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (M.op sF2 X1)
       have i₂ := eq16 sF2 X1 x
       grind)
    | (have i₁ := eq182 (M.op X0 sF2)
       have i₂ := eq16 X0 X1 sF2
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq272 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq202 eq254
    | exact resolve eq254 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq254
  have eq330 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
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
  have eq341 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
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
  have eq426 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq218 (M.op sF3 X1)
       have i₂ := eq16 sF3 X1 x
       grind)
    | (have i₁ := eq218 (M.op X0 sF3)
       have i₂ := eq16 X0 X1 sF3
       grind)
    | exact superpose eq16 eq218
    | exact resolve eq218 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ y) X1)) := by
    intro X1
    first
    | exact superpose eq218 eq16
    | exact resolve eq16 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ y) X1) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq218 eq16
    | exact resolve eq16 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | exact superpose eq218 eq433
    | exact resolve eq433 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq433
  have eq490 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq431 eq16
    | exact resolve eq16 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq435 eq490
    | exact resolve eq490 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq490
  have eq573 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq431 eq503
    | exact resolve eq503 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq595 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | (have i₁ := eq16 X0 x X2
       have i₂ := eq503 X0 x
       grind)
    | (have i₁ := eq16 (σ x) (σ y) X2
       have i₂ := eq503 X0 x
       grind)
    | exact superpose eq503 eq16
    | exact resolve eq16 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq573 eq174
    | exact resolve eq174 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq573
  have eq734 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq758 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq992 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq759 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq759
    | (have j0 := eq759 (σ X0)
       grind)
    | exact resolve eq759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9186 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq734
       grind)
    | exact superpose eq734 eq40
    | exact resolve eq40 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq9187 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9186
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9186
    | exact resolve eq9186 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9186
  have eq9189 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq9187
    | exact resolve eq9187 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9187
  have eq23237 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) ≠ (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq664 eq992
    | (have j0 := eq992 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq992 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq23273 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by grind
  clear eq23237
  have eq23394 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq23273 eq178
    | exact resolve eq178 eq23273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq23412 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq23273 eq272
    | exact resolve eq272 eq23273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23421 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq23273 eq23412
    | exact resolve eq23412 eq23273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23412
  have eq23438 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq23273 eq23394
    | exact resolve eq23394 eq23273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23394
  have eq23454 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X1
    first
    | (have i₁ := eq23438 x X1
       have i₂ := eq595 X1 x
       grind)
    | exact superpose eq595 eq23438
    | exact resolve eq23438 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23438
  have eq23688 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq23454 eq23273
    | exact resolve eq23273 eq23454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9189 eq747
    | exact resolve eq747 eq9189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9189
  have eq24844 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24836
       have r₂ := eq27
       grind)
    | exact resolve eq24836 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24836
  have eq24851 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24844 eq341
    | exact resolve eq341 eq24844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq24844
  have eq24901 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq24851
    | exact resolve eq24851 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24851
  have eq24918 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq24901
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq24901
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq24901
       have r₂ := eq13 x y
       grind)
    | exact resolve eq24901 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24901
  have eq24925 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24918 eq330
    | exact resolve eq330 eq24918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq24918
  have eq24981 : y = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq24925
    | exact resolve eq24925 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq24925
  have eq24997 : y = (k y y) ∨ y = (k x y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq24981
       have r₂ := eq13 x y
       grind)
    | exact resolve eq24981 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24981
  have eq25322 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq992 y
       have i₂ := eq24997
       grind)
    | exact superpose eq24997 eq992
    | (have j0 := eq992 y
       grind)
    | exact resolve eq992 eq24997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq25326 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq759 y
       have i₂ := eq24997
       grind)
    | exact superpose eq24997 eq759
    | (have j0 := eq759 y
       grind)
    | (have r₁ := eq759 y
       have r₂ := eq24997
       grind)
    | exact resolve eq759 eq24997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759 eq24997
  have eq25329 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq25326
  have eq25331 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by grind
  clear eq25322
  have eq25332 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq25331
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25331
    | exact resolve eq25331 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25331
  have eq25343 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq734
       have i₂ := eq25329
       grind)
    | exact superpose eq25329 eq734
    | exact resolve eq734 eq25329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq25329
  have eq25348 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq25343
  have eq25380 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq25332 eq272
    | exact resolve eq272 eq25332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25384 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq25332 eq595
    | exact resolve eq595 eq25332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25387 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq25332 eq25384
    | exact resolve eq25384 eq25332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25384
  have eq25389 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq25332 eq25380
    | exact resolve eq25380 eq25332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25332 eq25380
  have eq25408 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq25389
    | exact resolve eq25389 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25389
  have eq25423 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25387 eq25408
    | exact resolve eq25408 eq25387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25387 eq25408
  have eq25432 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq25423
       grind)
    | exact superpose eq25423 eq35
    | exact resolve eq35 eq25423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq25423
  have eq25436 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25432
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25432
    | exact resolve eq25432 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25432
  have eq25445 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25436 eq747
    | exact resolve eq747 eq25436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq25436
  have eq25451 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq25445
  have eq26206 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq249 y y
       have i₂ := eq25348
       grind)
    | exact superpose eq25348 eq249
    | exact resolve eq249 eq25348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26208 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq426 y y
       have i₂ := eq25348
       grind)
    | exact superpose eq25348 eq426
    | exact resolve eq426 eq25348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq26211 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq595 y y
       have i₂ := eq25348
       grind)
    | exact superpose eq25348 eq595
    | exact resolve eq595 eq25348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26214 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25348 eq26211
    | exact resolve eq26211 eq25348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26211
  have eq26217 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25348 eq26208
    | exact resolve eq26208 eq25348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26208
  have eq26219 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25348 eq26206
    | exact resolve eq26206 eq25348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25348 eq26206
  have eq26237 : y = (M.op (σ y) y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26214 eq26217
    | exact resolve eq26217 eq26214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26217
  have eq26239 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26219
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26219
    | exact resolve eq26219 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26219
  have eq26479 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26214 eq23421
    | exact resolve eq23421 eq26214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23421
  have eq26482 : y = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26214 eq23688
    | exact resolve eq23688 eq26214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26544 : y = (M.op x x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq26482
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26482
    | exact resolve eq26482 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26482
  have eq26547 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26479
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26479
    | exact resolve eq26479 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26479
  have eq26575 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq26547
    | exact resolve eq26547 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26547
  have eq26592 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26544 eq26575
    | exact resolve eq26575 eq26544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26544 eq26575
  have eq26634 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq595 x x
       have i₂ := eq26592
       grind)
    | exact superpose eq26592 eq595
    | exact resolve eq595 eq26592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26637 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26634
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26634
    | exact resolve eq26634 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26634
  have eq26849 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26637 eq23688
    | exact resolve eq23688 eq26637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26637
  have eq26914 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq26849
    | exact resolve eq26849 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26849
  have eq26992 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26914 eq23688
    | exact resolve eq23688 eq26914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27007 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26 eq26992
    | exact resolve eq26992 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26992
  have eq27038 : (σ y) = (σ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26914 eq27007
    | exact resolve eq27007 eq26914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26914 eq27007
  have eq29177 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op (σ y) y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26237 eq249
    | exact resolve eq249 eq26237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq29189 : (M.op (σ x) (σ y)) = (M.op x (M.op (σ y) y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26592 eq29177
    | exact resolve eq29177 eq26592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29177
  have eq29214 : (M.op (σ x) (σ y)) = (M.op x (M.op (σ y) y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq29189
    | exact resolve eq29189 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29189
  have eq29237 : (σ y) = (M.op x (M.op (σ y) y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26592 eq29214
    | exact resolve eq29214 eq26592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26592 eq29214
  have eq29258 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26237 eq29237
    | exact resolve eq29237 eq26237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26237 eq29237
  have eq29277 : y = (M.op x x) ∨ y = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq29258
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29258
    | exact resolve eq29258 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29258
  have eq29338 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq595 x x
       have i₂ := eq29277
       grind)
    | exact superpose eq29277 eq595
    | exact resolve eq595 eq29277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29277
  have eq29341 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq29338
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29338
    | exact resolve eq29338 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29338
  have eq29454 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29341 eq23688
    | exact resolve eq23688 eq29341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23688 eq29341
  have eq29523 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq29454
    | exact resolve eq29454 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29454
  have eq29655 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29523 eq27038
    | exact resolve eq27038 eq29523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27038 eq29523
  have eq29662 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq29655
  have eq29668 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq29662
    | exact resolve eq29662 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29662
  have eq29669 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq29668
  have eq31641 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26239 eq26214
    | exact resolve eq26214 eq26239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26214 eq26239
  have eq31674 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq31641
  have eq31757 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq595 x x
       have i₂ := eq31674
       grind)
    | exact superpose eq31674 eq595
    | exact resolve eq595 eq31674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31674
  have eq31760 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31757
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31757
    | exact resolve eq31757 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31757
  have eq32935 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25451 eq272
    | exact resolve eq272 eq25451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq32939 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25451 eq595
    | exact resolve eq595 eq25451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32942 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25451 eq32939
    | exact resolve eq32939 eq25451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32939
  have eq32944 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25451 eq32935
    | exact resolve eq32935 eq25451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25451 eq32935
  have eq32963 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq32944
    | exact resolve eq32944 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32944
  have eq32978 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32942 eq32963
    | exact resolve eq32963 eq32942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32942 eq32963
  have eq32979 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32978
  have eq33017 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32979 eq595
    | exact resolve eq595 eq32979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq32979
  have eq33020 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq33017
    | exact resolve eq33017 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33017
  have eq33636 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33020 eq31760
    | exact resolve eq31760 eq33020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33020
  have eq34368 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33636 eq31760
    | exact resolve eq31760 eq33636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31760 eq33636
  have eq34370 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq34368
  have eq34376 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq34370
    | exact resolve eq34370 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34370
  have eq34377 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq34376
  have eq34414 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34377 eq27
    | exact resolve eq27 eq34377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34377
  have eq34502 : y = (M.op x y) := by
    first
    | (have r₁ := eq34414
       have r₂ := eq29669
       grind)
    | exact resolve eq34414 eq29669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29669 eq34414
  have eq34518 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq34502
       grind)
    | exact superpose eq34502 eq18
    | exact resolve eq18 eq34502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq34519 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq34502
       grind)
    | exact superpose eq34502 eq24
    | exact resolve eq24 eq34502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq34502
  have eq34561 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34519 eq20
    | exact resolve eq20 eq34519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34519
  have eq34993 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq34518 eq214
    | exact resolve eq214 eq34518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq34518
  have eq35080 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq34993 eq23273
    | exact resolve eq23273 eq34993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23273
  have eq35086 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq34993 eq23454
    | exact resolve eq23454 eq34993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23454
  have eq35125 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq34993 eq503
    | exact resolve eq503 eq34993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq34993
  have eq35158 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq35086
    | (have j0 := eq35086 X0
       grind)
    | exact resolve eq35086 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35086
  have eq35164 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35080
    | exact resolve eq35080 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq35080
  have eq35179 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq34561 eq35158
    | exact resolve eq35158 eq34561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35158
  have eq35185 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq34561 eq35164
    | exact resolve eq35164 eq34561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35164
  have eq35190 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq35179 eq35185
    | exact resolve eq35185 eq35179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35179 eq35185
  have eq35198 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq35190 eq26
    | exact resolve eq26 eq35190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq35341 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35125 eq35198
    | exact resolve eq35198 eq35125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35125 eq35198
  have eq35422 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq35341 eq27
    | exact resolve eq27 eq35341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq35341
  have eq35500 : (M.op x y) ≠ (σ y) := by
    first
    | exact superpose eq34561 eq35422
    | exact resolve eq35422 eq34561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34561 eq35422
  have eq35511 : False := by grind
  exact eq35511

/-- `Equation4308`: `x ◇ (x ◇ y) = z ◇ (z ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation4308 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4308 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4308.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
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
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq181 x x
       have i₂ := eq182 x x
       grind)
    | (have i₁ := eq181 (σ x) (σ y)
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq181
    | (have j0 := eq181 (σ x) (σ y)
       have j1 := eq182 x y
       grind)
    | exact resolve eq181 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq189 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq182 X0 (M.op X0 x)
       have i₂ := eq182 X0 x
       grind)
    | (have i₁ := eq182 (σ x) (M.op (σ x) (σ y))
       have i₂ := eq182 X0 x
       grind)
    | exact superpose eq182 eq182
    | exact resolve eq182 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq196 eq189
    | exact resolve eq189 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq412 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq627 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq196 eq28
    | (have j0 := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq196 X0
       grind)
    | exact resolve eq28 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq628 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq627 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq634 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq182 X0 X0
       have i₂ := eq628 X0
       grind)
    | exact superpose eq628 eq182
    | exact resolve eq182 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) ≠ X1 ∨ (k X0 X1) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq628 X0
       grind)
    | exact superpose eq628 eq13
    | (have r₁ := eq13 X0 (k X0 (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq628 X0
       grind)
    | exact resolve eq13 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq661 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq628 X0
       grind)
    | exact superpose eq628 eq11
    | exact resolve eq11 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq662 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq724 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq706 X0
       have j1 := eq639 X0 X0
       grind)
    | (have r₁ := eq706 X0
       have r₂ := eq639 X0 (k X0 X0)
       grind)
    | (have r₁ := eq706 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq639 (M.op (σ x) (M.op (σ x) (σ y))) (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq706 x
       have r₂ := eq639 x x
       grind)
    | exact resolve eq706 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq706
  have eq741 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq634 (M.op sF2 sF4)
       have i₂ := eq724 (M.op sF2 sF4)
       grind)
    | exact superpose eq724 eq634
    | exact resolve eq634 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq742 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq628 (M.op sF2 sF4)
       have i₂ := eq724 (M.op sF2 sF4)
       grind)
    | exact superpose eq724 eq628
    | exact resolve eq628 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : ∀ X0 : G, (τ (k (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq412 X0 (σ X0)
       have i₂ := eq724 (σ X0)
       grind)
    | (have i₁ := eq412 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have i₂ := eq724 (σ X0)
       grind)
    | exact superpose eq724 eq412
    | exact resolve eq412 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq759 : ∀ X0 : G, (k X0 X0) = (τ (k (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq755 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq755
    | exact resolve eq755 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq772 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq759 X0
       have i₂ := eq412 X0 (M.op sF2 sF4)
       grind)
    | exact superpose eq412 eq759
    | exact resolve eq759 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq826 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq741 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq741
    | exact resolve eq741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1259 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq224 eq826
    | exact resolve eq826 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1259
       have i₂ := eq628 (σ (M.op sF2 sF4))
       grind)
    | exact superpose eq628 eq1259
    | exact resolve eq1259 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq1259
  have eq2273 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq659
       grind)
    | exact superpose eq659 eq41
    | exact resolve eq41 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq659
  have eq2275 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2273
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2273
    | exact resolve eq2273 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273
  have eq2277 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2275
    | exact resolve eq2275 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2279 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2277
       have i₂ := eq742 x
       grind)
    | exact superpose eq742 eq2277
    | exact resolve eq2277 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277
  have eq2750 : (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1291 eq412
    | exact resolve eq412 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq1291
  have eq2759 : (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq772 eq2750
    | exact resolve eq2750 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq2750
  have eq2762 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq224 eq2759
    | exact resolve eq2759 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq2759
  have eq2773 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2762 eq14
    | exact resolve eq14 eq2762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2279 eq661
    | exact resolve eq661 eq2279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq2279
  have eq3247 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3238
       have r₂ := eq27
       grind)
    | exact resolve eq3238 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3238
  have eq3251 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3247
       have i₂ := eq742 sF2
       grind)
    | exact superpose eq742 eq3247
    | exact resolve eq3247 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq3247
  have eq3253 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3251 eq98
    | exact resolve eq98 eq3251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq3251
  have eq3269 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq3253
    | exact resolve eq3253 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3253
  have eq3270 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3269
  have eq3279 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq741 x
       have i₂ := eq3270
       grind)
    | exact superpose eq3270 eq741
    | exact resolve eq741 eq3270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq3282 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq826 x
       have i₂ := eq3270
       grind)
    | exact superpose eq3270 eq826
    | exact resolve eq826 eq3270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826 eq3270
  have eq3286 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3282
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3282
    | exact resolve eq3282 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3282
  have eq3287 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3279
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3279
    | exact resolve eq3279 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279
  have eq3291 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3286
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3286
    | exact resolve eq3286 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3286
  have eq3294 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3291
    | exact resolve eq3291 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291
  have eq3295 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3287 eq3294
    | exact resolve eq3294 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3294
  have eq3298 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3295 eq196
    | exact resolve eq196 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq3341 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3295 eq2762
    | exact resolve eq2762 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3343 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq3346 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3341
    | exact resolve eq3341 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341
  have eq3389 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq3298
    | (have j0 := eq3298 X0
       grind)
    | exact resolve eq3298 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298
  have eq3392 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3295 eq3346
    | exact resolve eq3346 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq3433 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3295 eq3389
    | exact resolve eq3389 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295 eq3389
  have eq3435 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq3392
    | exact resolve eq3392 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392
  have eq3534 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3435 eq27
    | exact resolve eq27 eq3435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3435
  have eq4042 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3287 eq2773
    | exact resolve eq2773 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287
  have eq4055 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq4042
    | exact resolve eq4042 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4042
  have eq4219 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4055 eq2762
    | exact resolve eq2762 eq4055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762
  have eq4227 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq4219
    | exact resolve eq4219 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4219
  have eq4274 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4055 eq4227
    | exact resolve eq4227 eq4055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4227
  have eq4318 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq4274
    | exact resolve eq4274 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4274
  have eq4352 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4318
       have r₂ := eq3534
       grind)
    | exact resolve eq4318 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3534 eq4318
  have eq4378 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4352
       grind)
    | exact superpose eq4352 eq18
    | exact resolve eq18 eq4352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4389 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq4352
  have eq4828 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3433 eq4378
    | exact resolve eq4378 eq3433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3433 eq4378
  have eq4831 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq4828
  have eq4836 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4831
       have r₂ := eq3343
       grind)
    | exact resolve eq4831 eq3343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343 eq4831
  have eq4847 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4836 eq27
    | exact resolve eq27 eq4836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4895 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4836 eq4055
    | exact resolve eq4055 eq4836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4055 eq4836
  have eq4896 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq4895
  have eq4900 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4896
       have r₂ := eq4389
       grind)
    | exact resolve eq4896 eq4389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4389 eq4896
  have eq4934 : y = (M.op x y) := by
    first
    | (have r₁ := eq4900
       have r₂ := eq4847
       grind)
    | exact resolve eq4900 eq4847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4847 eq4900
  have eq4960 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4934
       grind)
    | exact superpose eq4934 eq18
    | exact resolve eq18 eq4934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4961 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4934
       grind)
    | exact superpose eq4934 eq24
    | exact resolve eq24 eq4934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4934
  have eq5108 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4960 eq187
    | exact resolve eq187 eq4960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq4960
  have eq5169 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5108 eq2773
    | exact resolve eq2773 eq5108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773
  have eq5174 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq5108 eq182
    | exact resolve eq182 eq5108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq5108
  have eq5580 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq5169 eq4961
    | exact resolve eq4961 eq5169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4961
  have eq5581 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5169 eq20
    | exact resolve eq20 eq5169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5169
  have eq5648 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq5580 eq26
    | exact resolve eq26 eq5580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5580
  have eq5694 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5174 eq5648
    | exact resolve eq5648 eq5174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5174 eq5648
  have eq5777 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq5694 eq27
    | exact resolve eq27 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5694
  have eq5872 : False := by grind
  exact eq5872

/-- `Equation4308`: `x ◇ (x ◇ y) = z ◇ (z ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4308 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4308 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4308.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq86 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq123 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq218 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq51 X0 (M.op X0 x)
       have i₂ := eq51 X0 x
       grind)
    | (have i₁ := eq51 x (M.op x y)
       have i₂ := eq51 X0 x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq51 x x
       grind)
    | (have i₁ := eq52 x y
       have i₂ := eq51 x x
       grind)
    | exact superpose eq51 eq52
    | (have j0 := eq52 x y
       have j1 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq374 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq218 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq218 X0
       grind)
    | exact resolve eq13 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq806 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq85 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq817 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq806 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq806 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq806 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq806 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq836 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq817 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq817
    | (have j0 := eq817 X0 X1
       grind)
    | exact resolve eq817 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq3323 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq86 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq86
    | (have j0 := eq86 x
       grind)
    | exact resolve eq86 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq3332 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3323
  have eq3339 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3332
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3332
    | exact resolve eq3332 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3332
  have eq3356 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3339
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3339 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3339
  have eq3361 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3356 eq50
    | exact resolve eq50 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq3356
  have eq6367 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq836 X0 (M.op X0 X0)
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq836
    | (have j0 := eq836 X0 (M.op X0 X0)
       grind)
    | exact resolve eq836 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq836
  have eq6485 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6367
  have eq6486 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6485 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6485
  have eq7113 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6486 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6486
    | (have j0 := eq6486 x
       grind)
    | exact resolve eq6486 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7117 : ∀ X0 : G, (k (σ X0) (M.op x (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6486 X0
       have i₂ := eq378 (σ X0)
       grind)
    | exact superpose eq378 eq6486
    | exact resolve eq6486 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7122 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0) (σ X0)
       have i₂ := eq6486 X0
       grind)
    | exact superpose eq6486 eq51
    | exact resolve eq51 eq6486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6486
  have eq7321 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq7113
       grind)
    | exact superpose eq7113 eq16
    | exact resolve eq16 eq7113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7113
  have eq7348 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq3361 eq7321
    | exact resolve eq7321 eq3361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7321
  have eq9133 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq218 eq7122
    | exact resolve eq7122 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9170 : (M.op x (M.op x y)) = (k (σ (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq9133
       have i₂ := eq378 (σ (M.op x sF0))
       grind)
    | exact superpose eq378 eq9133
    | exact resolve eq9133 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq9133
  have eq9257 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | exact superpose eq7117 eq9170
    | exact resolve eq9170 eq7117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7117 eq9170
  have eq9335 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq218 eq9257
    | exact resolve eq9257 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9257
  have eq9341 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq9335 eq16
    | exact resolve eq16 eq9335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq14200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14199
    | exact resolve eq14199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14199
  have eq14213 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14200
       have r₂ := eq28
       grind)
    | exact resolve eq14200 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14200
  have eq14218 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14213
    | exact resolve eq14213 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14213
  have eq14220 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14218 eq3361
    | exact resolve eq3361 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3361 eq14218
  have eq14234 : (τ (σ y)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14220
       have i₂ := eq7348
       grind)
    | exact superpose eq7348 eq14220
    | exact resolve eq14220 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7348 eq14220
  have eq14238 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq14234
    | exact resolve eq14234 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14234
  have eq14239 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14238
  have eq14243 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7122 x
       have i₂ := eq14239
       grind)
    | exact superpose eq14239 eq7122
    | exact resolve eq7122 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7122
  have eq14245 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 x x
       have i₂ := eq14239
       grind)
    | exact superpose eq14239 eq51
    | exact resolve eq51 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq14239
  have eq14252 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14245
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14245
    | exact resolve eq14245 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14245
  have eq14253 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14243
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14243
    | exact resolve eq14243 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14243
  have eq14257 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14253
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14253
    | exact resolve eq14253 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14253
  have eq14258 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14257
    | exact resolve eq14257 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14257
  have eq14511 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14252 eq9335
    | exact resolve eq9335 eq14252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14520 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq14511
    | exact resolve eq14511 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14511
  have eq14524 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14520 eq232
    | exact resolve eq232 eq14520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14527 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14524
    | exact resolve eq14524 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14524
  have eq14808 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14258 eq14252
    | exact resolve eq14252 eq14258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14252 eq14258
  have eq14815 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14808
  have eq14821 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14815 eq232
    | exact resolve eq232 eq14815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq14823 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq14825 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14821
    | exact resolve eq14821 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14821
  have eq15780 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14527 eq218
    | exact resolve eq218 eq14527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15792 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14527 eq9341
    | exact resolve eq9341 eq14527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14527
  have eq16054 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14520 eq15792
    | exact resolve eq15792 eq14520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15792
  have eq16088 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq16054
  have eq16091 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq16088
    | exact resolve eq16088 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16088
  have eq16455 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14825 eq218
    | exact resolve eq218 eq14825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16467 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14825 eq9341
    | exact resolve eq9341 eq14825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9341 eq14825
  have eq16545 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14815 eq16467
    | exact resolve eq16467 eq14815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16467
  have eq16581 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq16545
  have eq16584 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16581
       have r₂ := eq14823
       grind)
    | exact resolve eq16581 eq14823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16581
  have eq16585 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq16584
    | exact resolve eq16584 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16584
  have eq16588 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq16585 eq28
    | exact resolve eq28 eq16585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16585
  have eq16606 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16588
       have r₂ := eq16091
       grind)
    | exact resolve eq16588 eq16091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16091 eq16588
  have eq16928 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14520 eq15780
    | exact resolve eq15780 eq14520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14520 eq15780
  have eq16940 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq16928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16928
  have eq16949 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14815 eq16455
    | exact resolve eq16455 eq14815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14815 eq16455
  have eq16963 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq16949 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16949
  have eq16969 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq16963 X0
       grind)
    | (have r₁ := eq16963 X0
       have r₂ := eq14823
       grind)
    | exact resolve eq16963 eq14823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14823 eq16963
  have eq17006 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16606 eq16940
    | exact resolve eq16940 eq16606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16940
  have eq17024 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17006 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17006
  have eq17068 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16606 eq16969
    | exact resolve eq16969 eq16606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16606 eq16969
  have eq17086 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17068 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17068
  have eq17414 : y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17024 x
       grind)
    | exact superpose eq17024 eq19
    | (have j1 := eq17024 x
       grind)
    | exact resolve eq19 eq17024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17024
  have eq17420 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq17414
  have eq17729 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17086 x
       grind)
    | exact superpose eq17086 eq19
    | (have j1 := eq17086 x
       grind)
    | exact resolve eq19 eq17086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17086
  have eq17735 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17729
  have eq17748 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17735 eq28
    | exact resolve eq28 eq17735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17735
  have eq17773 : y = (M.op x y) := by
    first
    | (have r₁ := eq17748
       have r₂ := eq17420
       grind)
    | exact resolve eq17748 eq17420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17420 eq17748
  have eq17775 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17773 eq21
    | exact resolve eq21 eq17773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17821 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17773 eq218
    | exact resolve eq218 eq17773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq17841 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17773 eq9335
    | exact resolve eq9335 eq17773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9335
  have eq17845 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq17841
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17841
    | exact resolve eq17841 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17841
  have eq17863 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq17821 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17821
    | (have j0 := eq17821 X0
       grind)
    | exact resolve eq17821 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17821
  have eq17908 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq17775
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17775
    | exact resolve eq17775 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17775
  have eq17910 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq17845
    | exact resolve eq17845 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17845
  have eq17921 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq17773 eq17863
    | exact resolve eq17863 eq17773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17863
  have eq17947 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq17773 eq17910
    | exact resolve eq17910 eq17773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17773 eq17910
  have eq17968 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17908 eq27
    | exact resolve eq27 eq17908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17908
  have eq18491 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq17947 eq17968
    | exact resolve eq17968 eq17947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17968
  have eq18492 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18491
       have i₂ := eq17921 sF2
       grind)
    | exact superpose eq17921 eq18491
    | exact resolve eq18491 eq17921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17921 eq18491
  have eq18497 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq18492 eq28
    | exact resolve eq28 eq18492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18492
  have eq18527 : False := by grind
  exact eq18527

/-- `Equation4308`: `x ◇ (x ◇ y) = z ◇ (z ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4308 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4308 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4308.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq163 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq212 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq51 X0 (M.op X0 x)
       have i₂ := eq51 X0 x
       grind)
    | (have i₁ := eq51 x (M.op x y)
       have i₂ := eq51 X0 x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq369 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq212 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq212 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq369 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq437 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq51 X0 X0
       have i₂ := eq370 X0
       grind)
    | exact superpose eq370 eq51
    | exact resolve eq51 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq81 X0 X0
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq81 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq572 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq567 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq576 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq572 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq572 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq572 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq3075 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq370 eq576
    | (have j0 := eq576 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq576 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq3090 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq212 eq3075
    | (have j0 := eq3075 X0
       grind)
    | exact resolve eq3075 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq3091 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3090 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3090
  have eq3118 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3091 eq318
    | exact resolve eq318 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq3123 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3091 eq36
    | exact resolve eq36 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3124 : (M.op (σ y) (σ y)) = (σ (k y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3091 eq37
    | exact resolve eq37 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3091
  have eq3147 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq370 eq3124
    | exact resolve eq3124 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124
  have eq3148 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq370 eq3123
    | exact resolve eq3123 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123
  have eq3167 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3147
       grind)
    | exact superpose eq3147 eq16
    | exact resolve eq16 eq3147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3147
  have eq3190 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3148
       grind)
    | exact superpose eq3148 eq16
    | exact resolve eq16 eq3148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3148
  have eq3399 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq163 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq163
    | (have j0 := eq163 x
       grind)
    | exact resolve eq163 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq3405 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3399
  have eq3410 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3405
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3405
    | exact resolve eq3405 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3405
  have eq3488 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3410
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq3410 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410
  have eq3494 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3488 eq50
    | exact resolve eq50 eq3488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq3488
  have eq3565 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq3494 eq3190
    | exact resolve eq3190 eq3494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3190
  have eq3871 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq370 eq3118
    | exact resolve eq3118 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3876 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3118 eq437
    | exact resolve eq437 eq3118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq3956 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3871 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3871
    | exact resolve eq3871 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871
  have eq4332 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq3956 X0
       grind)
    | exact superpose eq3956 eq15
    | exact resolve eq15 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq4648 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0) (σ X0)
       have i₂ := eq4332 X0
       grind)
    | exact superpose eq4332 eq51
    | exact resolve eq51 eq4332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4332
  have eq4993 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq212 eq3876
    | exact resolve eq3876 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3876
  have eq5018 : (M.op x (M.op x y)) = (k (τ (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq4993
       have i₂ := eq370 (τ (M.op x sF0))
       grind)
    | exact superpose eq370 eq4993
    | exact resolve eq4993 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq4993
  have eq5033 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3118 eq5018
    | exact resolve eq5018 eq3118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118 eq5018
  have eq5042 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq212 eq5033
    | exact resolve eq5033 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5033
  have eq5044 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq5042 eq15
    | exact resolve eq15 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042
  have eq26350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq26351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq26350
    | exact resolve eq26350 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26350
  have eq26362 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq26351
       have r₂ := eq28
       grind)
    | exact resolve eq26351 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26351
  have eq26366 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26362 eq3167
    | exact resolve eq3167 eq26362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167 eq26362
  have eq26396 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq26366
    | exact resolve eq26366 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26366
  have eq26397 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq26396
  have eq26402 : (τ (σ y)) = (k x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26397 eq3494
    | exact resolve eq3494 eq26397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3494 eq26397
  have eq26430 : (τ (σ y)) = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26402
       have i₂ := eq3565
       grind)
    | exact superpose eq3565 eq26402
    | exact resolve eq26402 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3565 eq26402
  have eq26437 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq26430
    | exact resolve eq26430 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq26430
  have eq26438 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq26437
  have eq26453 : (M.op x (M.op x y)) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51 y y
       have i₂ := eq26438
       grind)
    | exact superpose eq26438 eq51
    | exact resolve eq51 eq26438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26832 : y = (M.op x (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26438
       have i₂ := eq26453
       grind)
    | exact superpose eq26453 eq26438
    | exact resolve eq26438 eq26453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26438 eq26453
  have eq26841 : y = (M.op x (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq26832
  have eq26897 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26841 eq51
    | exact resolve eq51 eq26841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26841
  have eq26902 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26897
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26897
    | exact resolve eq26897 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26897
  have eq27288 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4648 x
       have i₂ := eq26902
       grind)
    | exact superpose eq26902 eq4648
    | exact resolve eq4648 eq26902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4648
  have eq27290 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 x x
       have i₂ := eq26902
       grind)
    | exact superpose eq26902 eq51
    | exact resolve eq51 eq26902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq26902
  have eq27295 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27290
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27290
    | exact resolve eq27290 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27290
  have eq27296 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27288
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27288
    | exact resolve eq27288 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27288
  have eq27307 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27296
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27296
    | exact resolve eq27296 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq27296
  have eq27310 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq27307
    | exact resolve eq27307 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27307
  have eq27389 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27295 eq5044
    | exact resolve eq5044 eq27295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27424 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq27389
    | exact resolve eq27389 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27389
  have eq27955 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27310 eq27295
    | exact resolve eq27295 eq27310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27295 eq27310
  have eq27959 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq27955
  have eq27964 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27959 eq28
    | exact resolve eq28 eq27959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27959
  have eq27965 : y = (M.op x y) := by
    first
    | (have r₁ := eq27964
       have r₂ := eq27424
       grind)
    | exact resolve eq27964 eq27424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27424 eq27964
  have eq28315 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27965 eq21
    | exact resolve eq21 eq27965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28358 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq27965 eq212
    | exact resolve eq212 eq27965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq28392 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27965 eq5044
    | exact resolve eq5044 eq27965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5044
  have eq28453 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq28392
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28392
    | exact resolve eq28392 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28392
  have eq28486 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq28358 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28358
    | (have j0 := eq28358 X0
       grind)
    | exact resolve eq28358 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28358
  have eq28529 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28315
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28315
    | exact resolve eq28315 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28315
  have eq28553 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq28453
    | exact resolve eq28453 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq28453
  have eq28572 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq27965 eq28486
    | exact resolve eq28486 eq27965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28486
  have eq28602 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq27965 eq28553
    | exact resolve eq28553 eq27965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27965 eq28553
  have eq28623 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq28529 eq27
    | exact resolve eq27 eq28529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28529
  have eq29332 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq28602 eq28623
    | exact resolve eq28623 eq28602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28623
  have eq29333 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29332
       have i₂ := eq28572 sF2
       grind)
    | exact superpose eq28572 eq29332
    | exact resolve eq29332 eq28572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28572 eq29332
  have eq29337 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq29333 eq28
    | exact resolve eq28 eq29333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq29333
  have eq29340 : False := by grind
  exact eq29340

/-- `Equation4311`: `x ◇ (x ◇ y) = z ◇ (w ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_y_pxx_pxy_Equation4311 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4311 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4311.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op x y)) := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq79
    | exact resolve eq79 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq216 : (M.op x (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq47 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47
    | (have j0 := eq47 y x
       grind)
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op x X0) X2 X3
       have i₂ := eq47 X0 x
       grind)
    | exact superpose eq47 eq14
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq227 X0 x x
       have i₂ := eq47 x x
       grind)
    | exact superpose eq47 eq227
    | exact resolve eq227 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq235 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq48 x x
       have i₂ := eq47 x x
       grind)
    | exact superpose eq47 eq48
    | exact resolve eq48 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq246 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq216 eq53
    | exact resolve eq53 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq216
  have eq811 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq71 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq71 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq71 X1 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq821 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq811 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq827 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq821 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq821 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq821 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq821 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq837 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq827
    | (have j0 := eq827 X0 X1
       grind)
    | exact resolve eq827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq6411 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq837
  have eq6526 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6411 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6411
  have eq6527 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6526 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526
  have eq6969 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6527 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6527
    | (have j0 := eq6527 x
       grind)
    | exact resolve eq6527 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6980 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq47 (σ X0) (σ X0)
       have i₂ := eq6527 X0
       grind)
    | exact superpose eq6527 eq47
    | exact resolve eq47 eq6527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq6996 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq6969
       grind)
    | exact superpose eq6969 eq16
    | exact resolve eq16 eq6969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6969
  have eq7486 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq228 eq6980
    | exact resolve eq6980 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7521 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq7486
       have i₂ := eq6527 (M.op x sF0)
       grind)
    | exact superpose eq6527 eq7486
    | exact resolve eq7486 eq6527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6527 eq7486
  have eq7535 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq228 eq7521
    | exact resolve eq7521 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7521
  have eq7542 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq7535 eq16
    | exact resolve eq16 eq7535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq14403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14394
    | exact resolve eq14394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14394
  have eq14415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14403
       have r₂ := eq28
       grind)
    | exact resolve eq14403 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14403
  have eq14417 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14415
    | exact resolve eq14415 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14415
  have eq14419 : (τ (σ y)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14417 eq6996
    | exact resolve eq6996 eq14417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6996 eq14417
  have eq14443 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq14419
    | exact resolve eq14419 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14419
  have eq14444 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14443
  have eq14456 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6980 x
       have i₂ := eq14444
       grind)
    | exact superpose eq14444 eq6980
    | exact resolve eq6980 eq14444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6980
  have eq14462 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq246 x x
       have i₂ := eq14444
       grind)
    | exact superpose eq14444 eq246
    | exact resolve eq246 eq14444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq14444
  have eq14463 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14462
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14462
    | exact resolve eq14462 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14462
  have eq14467 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14456
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14456
    | exact resolve eq14456 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14456
  have eq14476 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14467
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14467
    | exact resolve eq14467 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14467
  have eq14477 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14476
    | exact resolve eq14476 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14476
  have eq14713 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14463 eq7535
    | exact resolve eq7535 eq14463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14734 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq14713
    | exact resolve eq14713 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14713
  have eq14737 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14734 eq235
    | exact resolve eq235 eq14734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14740 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14737
    | exact resolve eq14737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14737
  have eq15144 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14477 eq14463
    | exact resolve eq14463 eq14477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14463 eq14477
  have eq15154 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15144
  have eq15323 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15154 eq235
    | exact resolve eq235 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq15325 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq15327 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq15323
    | exact resolve eq15323 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15323
  have eq16465 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14740 eq228
    | exact resolve eq228 eq14740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16475 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14740 eq7542
    | exact resolve eq7542 eq14740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14740
  have eq16724 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14734 eq16475
    | exact resolve eq16475 eq14734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16475
  have eq16757 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq16724
  have eq16759 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq16757
    | exact resolve eq16757 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16757
  have eq17100 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15327 eq228
    | exact resolve eq228 eq15327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17110 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15327 eq7542
    | exact resolve eq7542 eq15327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7542 eq15327
  have eq17365 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15154 eq17110
    | exact resolve eq17110 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17110
  have eq17400 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq17365
  have eq17402 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17400
       have r₂ := eq15325
       grind)
    | exact resolve eq17400 eq15325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17400
  have eq17403 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq17402
    | exact resolve eq17402 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17402
  have eq17406 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq17403 eq28
    | exact resolve eq28 eq17403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17403
  have eq17427 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17406
       have r₂ := eq16759
       grind)
    | exact resolve eq17406 eq16759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16759 eq17406
  have eq17896 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14734 eq16465
    | exact resolve eq16465 eq14734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14734 eq16465
  have eq17916 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17896 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17896
  have eq17968 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15154 eq17100
    | exact resolve eq17100 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15154 eq17100
  have eq17990 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17968
  have eq17996 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17990 X0
       grind)
    | (have r₁ := eq17990 X0
       have r₂ := eq15325
       grind)
    | exact resolve eq17990 eq15325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15325 eq17990
  have eq18040 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17427 eq17916
    | exact resolve eq17916 eq17427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17916
  have eq18065 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18040
  have eq18146 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17427 eq17996
    | exact resolve eq17996 eq17427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17427 eq17996
  have eq18171 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18146
  have eq18857 : y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18065 x
       grind)
    | exact superpose eq18065 eq19
    | (have j1 := eq18065 x
       grind)
    | exact resolve eq19 eq18065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18065
  have eq18868 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq18857
  have eq20348 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18171 x
       grind)
    | exact superpose eq18171 eq19
    | (have j1 := eq18171 x
       grind)
    | exact resolve eq19 eq18171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18171
  have eq20359 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20348
  have eq20376 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20359 eq28
    | exact resolve eq28 eq20359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20359
  have eq20403 : y = (M.op x y) := by
    first
    | (have r₁ := eq20376
       have r₂ := eq18868
       grind)
    | exact resolve eq20376 eq18868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18868 eq20376
  have eq20404 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20403 eq21
    | exact resolve eq21 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20451 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20403 eq228
    | exact resolve eq228 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq20478 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20403 eq7535
    | exact resolve eq7535 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7535
  have eq20490 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq20478
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20478
    | exact resolve eq20478 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20478
  have eq20517 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq20451 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20451
    | (have j0 := eq20451 X0
       grind)
    | exact resolve eq20451 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20451
  have eq20563 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20404
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20404
    | exact resolve eq20404 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20404
  have eq20569 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq20490
    | exact resolve eq20490 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq20490
  have eq20580 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq20403 eq20517
    | exact resolve eq20517 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20517
  have eq20586 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq20403 eq20569
    | exact resolve eq20569 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20403 eq20569
  have eq20596 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20563 eq27
    | exact resolve eq27 eq20563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20563
  have eq21394 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq20586 eq20596
    | exact resolve eq20596 eq20586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20596
  have eq21395 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21394
       have i₂ := eq20580 sF2
       grind)
    | exact superpose eq20580 eq21394
    | exact resolve eq21394 eq20580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20580 eq21394
  have eq21400 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq21395 eq28
    | exact resolve eq28 eq21395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq21395
  have eq21433 : False := by grind
  exact eq21433
