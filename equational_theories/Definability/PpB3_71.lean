import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyx_pxy_Equation4419 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq45
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq76
    | exact resolve eq76 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq22 eq79
    | exact resolve eq79 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq96 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq92
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq96
  have eq118 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq39
    | (have j0 := eq39 (M.op x y)
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq121 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq118
  have eq122 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq121
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq36
  have eq298 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq287
    | exact resolve eq287 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq299 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq298
  have eq342 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq40
  have eq378 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq59 (M.op X0 y)
       have i₂ := eq212 X0 y
       grind)
    | (have i₁ := eq59 (M.op x y)
       have i₂ := eq212 X0 y
       grind)
    | exact superpose eq212 eq59
    | exact resolve eq59 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq212 X0 (M.op sF0 y)
       grind)
    | (have i₁ := eq378 x
       have i₂ := eq212 X0 (M.op sF0 y)
       grind)
    | exact superpose eq212 eq378
    | exact resolve eq378 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq391 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq381 X0
       have i₂ := eq59 sF0
       grind)
    | exact superpose eq59 eq381
    | exact resolve eq381 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq418 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq419 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq14
    | exact resolve eq14 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op X1 (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq14
    | exact resolve eq14 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq418 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq418
    | (have j0 := eq418 X0
       grind)
    | exact resolve eq418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq438 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq219 eq59
    | exact resolve eq59 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq219 eq60
    | exact resolve eq60 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq219 eq439
    | exact resolve eq439 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq441 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq219 eq438
    | exact resolve eq438 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq450 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq60 eq440
    | exact resolve eq440 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq451 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq441 X0
       have i₂ := eq59 sF4
       grind)
    | exact superpose eq59 eq441
    | exact resolve eq441 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq530 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 (M.op X0 y) X1 X2
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq56
    | exact resolve eq56 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X2 (σ X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (σ X0) (σ X0) X1 X2
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq56
    | exact resolve eq56 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq666 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq58 X1 X2 X3
       have i₂ := eq56 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq58 X1 X2 X3
       have i₂ := eq56 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq727 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq60 eq54
    | exact resolve eq54 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq219 eq728
    | (have j0 := eq728 X0 (σ x)
       grind)
    | exact resolve eq728 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq822 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq727 X0 x
       have i₂ := eq212 x X0
       grind)
    | (have i₁ := eq727 x x
       have i₂ := eq212 X0 x
       grind)
    | exact superpose eq212 eq727
    | (have j0 := eq727 X0 x
       grind)
    | exact resolve eq727 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq1181 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (M.op X0 X1)
       have i₂ := eq55 X1 y (M.op X0 X1) X0
       grind)
    | exact superpose eq55 eq59
    | exact resolve eq59 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (M.op x X0)
       have i₂ := eq55 X0 sF3 (M.op x X0) x
       grind)
    | exact superpose eq55 eq60
    | exact resolve eq60 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1229 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq219 eq1182
    | exact resolve eq1182 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1230 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1181 X0 X1
       have i₂ := eq212 (M.op X0 X1) (M.op X1 (M.op X1 y))
       grind)
    | exact superpose eq212 eq1181
    | exact resolve eq1181 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq1255 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq60 eq1229
    | exact resolve eq1229 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1256 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1230 X0 X1
       have i₂ := eq59 X1
       grind)
    | exact superpose eq59 eq1230
    | exact resolve eq1230 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1373 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq128 eq299
    | exact resolve eq299 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq16
    | exact resolve eq16 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1397 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq219 eq1373
    | exact resolve eq1373 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1398 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq450 eq1397
    | exact resolve eq1397 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1399 : (σ (M.op (M.op x y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1398
       have i₂ := eq212 y (M.op y y)
       grind)
    | exact superpose eq212 eq1398
    | exact resolve eq1398 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1400 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq391 eq1399
    | exact resolve eq1399 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1401 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq122 eq1400
    | exact resolve eq1400 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq2034 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq219 eq821
    | exact resolve eq821 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq2113 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2034 eq54
    | exact resolve eq54 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034
  have eq2132 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2113 X0
       have i₂ := eq14 sF4 sF3 sF4
       grind)
    | exact superpose eq14 eq2113
    | exact resolve eq2113 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq2136 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | (have i₁ := eq2132 x
       have i₂ := eq14 sF4 sF3 x
       grind)
    | exact superpose eq14 eq2132
    | exact resolve eq2132 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132
  have eq2137 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq450 eq2136
    | exact resolve eq2136 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2136
  have eq2138 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1401 eq2137
    | exact resolve eq2137 eq1401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137
  have eq2149 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq822 y
       have i₂ := eq212 sF0 y
       grind)
    | exact superpose eq212 eq822
    | exact resolve eq822 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq2200 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2149 eq54
    | exact resolve eq54 eq2149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2219 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2200 X0
       have i₂ := eq14 sF0 y sF0
       grind)
    | exact superpose eq14 eq2200
    | exact resolve eq2200 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq2223 : (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2219 x
       have i₂ := eq14 sF0 y x
       grind)
    | exact superpose eq14 eq2219
    | exact resolve eq2219 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219
  have eq2224 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq391 eq2223
    | exact resolve eq2223 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq2313 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq60 eq1255
    | exact resolve eq1255 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1255
  have eq2404 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq450 eq2313
    | exact resolve eq2313 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq2313
  have eq2421 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1401 eq2404
    | exact resolve eq2404 eq1401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401 eq2404
  have eq2429 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq2138 eq2421
    | exact resolve eq2421 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138 eq2421
  have eq2451 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2429 y
       have i₂ := eq59 sF4
       grind)
    | exact superpose eq59 eq2429
    | exact resolve eq2429 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429
  have eq2509 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq1256 X0 (M.op X0 y)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq1256
    | exact resolve eq1256 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq2624 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq391 eq2509
    | exact resolve eq2509 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509
  have eq2643 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2224 eq2624
    | exact resolve eq2624 eq2224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224 eq2624
  have eq2721 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1256 eq2643
    | exact resolve eq2643 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2722 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq451 eq2643
    | exact resolve eq2643 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq2643
  have eq3841 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) (M.op y y))) X0) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq419 (M.op y y) X0
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq419
    | exact resolve eq419 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq4007 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op y y) (M.op y y))) X0) := by
    intro X0
    first
    | exact superpose eq221 eq3841
    | exact resolve eq3841 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq3841
  have eq4041 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op x y) (M.op y y))) X0) := by
    intro X0
    first
    | (have i₁ := eq4007 X0
       have i₂ := eq212 y (M.op y y)
       grind)
    | exact superpose eq212 eq4007
    | exact resolve eq4007 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4007
  have eq4057 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq391 eq4041
    | exact resolve eq4041 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq4041
  have eq4069 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq122 eq4057
    | exact resolve eq4057 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq4057
  have eq4073 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq219 eq4069
    | exact resolve eq4069 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq4069
  have eq4075 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2451 eq4073
    | exact resolve eq4073 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451 eq4073
  have eq4077 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2722 eq4075
    | exact resolve eq4075 eq2722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722 eq4075
  have eq4496 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op y X1)) y) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq530 (M.op X2 X1) X3 y
       have i₂ := eq54 X2 X1 y X0
       grind)
    | exact superpose eq54 eq530
    | exact resolve eq530 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq4520 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq1256 eq530
    | exact resolve eq530 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4675 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (M.op x y) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq4077 eq4520
    | exact resolve eq4520 eq4077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4520
  have eq4691 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq4496 x X1 X2 X3
       have i₂ := eq212 (M.op x (M.op y X1)) X3
       grind)
    | exact superpose eq212 eq4496
    | exact resolve eq4496 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4496
  have eq4743 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4675 X0 X1
       have i₂ := eq530 X0 X1 sF0
       grind)
    | exact superpose eq530 eq4675
    | exact resolve eq4675 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq4675
  have eq4757 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq2721 eq4691
    | (have j0 := eq4691 y x X3
       grind)
    | exact resolve eq4691 eq2721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721 eq4691
  have eq4803 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (σ x) (σ y)) X3) := by
    intro X3
    first
    | exact superpose eq4077 eq4757
    | exact resolve eq4757 eq4077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4077 eq4757
  have eq5053 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq4803 eq4743
    | exact resolve eq4743 eq4803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4743 eq4803
  have eq6012 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5053 X1 X2
       have i₂ := eq56 sF0 X1 X2 x
       grind)
    | (have i₁ := eq5053 X1 X2
       have i₂ := eq56 X0 X1 X2 sF0
       grind)
    | exact superpose eq56 eq5053
    | exact resolve eq5053 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq6018 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5053 (σ X0) X1
       have i₂ := eq537 X0 X1 sF0
       grind)
    | exact superpose eq537 eq5053
    | exact resolve eq5053 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq7128 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1256 eq666
    | exact resolve eq666 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq1256
  have eq7435 : ∀ X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op x y) X2) := by
    intro X1 X2
    first
    | exact superpose eq5053 eq7128
    | exact resolve eq7128 eq5053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5053 eq7128
  have eq11875 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op x y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq420 X0 x
       have i₂ := eq6012 x (σ X0) (σ X0)
       grind)
    | exact superpose eq6012 eq420
    | exact resolve eq420 eq6012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq6012
  have eq15969 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (M.op x y) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq421 X0
       have i₂ := eq11875 X0
       grind)
    | exact superpose eq11875 eq421
    | (have j0 := eq421 X0
       grind)
    | exact resolve eq421 eq11875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq11875
  have eq21616 : ∀ X0 : G, (σ (M.op (M.op x y) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq7435 (τ X0) (τ X0)
       grind)
    | exact superpose eq7435 eq342
    | (have j0 := eq342 X0
       grind)
    | exact resolve eq342 eq7435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq7435
  have eq21617 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (M.op x y) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq21616 X0
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq21616
    | (have j0 := eq21616 X0
       grind)
    | exact resolve eq21616 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq21616
  have eq21618 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (M.op x y) (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21617 X0
       have i₂ := eq1388 X0
       grind)
    | exact superpose eq1388 eq21617
    | (have j0 := eq21617 X0
       grind)
    | exact resolve eq21617 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388 eq21617
  have eq24493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq24494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq28 eq24493
    | exact resolve eq24493 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24493
  have eq24505 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq24494
       have r₂ := eq29
       grind)
    | exact resolve eq24494 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24494
  have eq24509 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq24505 eq128
    | exact resolve eq128 eq24505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq24505
  have eq24594 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq24509
    | exact resolve eq24509 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24509
  have eq24595 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24594
  have eq24617 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq24595
       grind)
    | exact superpose eq24595 eq97
    | exact resolve eq97 eq24595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq24626 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq212 y X0
       have i₂ := eq24595
       grind)
    | exact superpose eq24595 eq212
    | exact resolve eq212 eq24595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq24636 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq6018 y X0
       have i₂ := eq24595
       grind)
    | exact superpose eq24595 eq6018
    | exact resolve eq6018 eq24595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6018
  have eq24648 : (σ (k x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15969 y
       have i₂ := eq24595
       grind)
    | exact superpose eq24595 eq15969
    | exact resolve eq15969 eq24595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15969 eq24595
  have eq24680 : (σ (k x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24648
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq24648
    | exact resolve eq24648 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24648
  have eq24686 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24636 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24636
    | (have j0 := eq24636 X0
       grind)
    | exact resolve eq24636 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24636
  have eq24700 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24617
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24617
    | exact resolve eq24617 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24617
  have eq24703 : (k (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24680
       have i₂ := eq50
       grind)
    | exact superpose eq50 eq24680
    | exact resolve eq24680 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq24680
  have eq24712 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24703
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq24703
    | exact resolve eq24703 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24703
  have eq24715 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24712
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24712
    | exact resolve eq24712 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24712
  have eq24716 : (k (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24715
  have eq24750 : (k (σ x) (σ y)) = (σ (M.op (M.op x y) (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24700 eq21618
    | exact resolve eq21618 eq24700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21618 eq24700
  have eq24782 : (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq24750
    | exact resolve eq24750 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24750
  have eq24809 : y = (τ (σ x)) ∨ (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq24782
    | exact resolve eq24782 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24782
  have eq24818 : x = y ∨ (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30 eq24809
    | exact resolve eq24809 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24809
  have eq24819 : (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq24818
  have eq26087 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq24686
    | (have j0 := eq24686 (σ y)
       grind)
    | exact resolve eq24686 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24686
  have eq30770 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24626 eq24819
    | exact resolve eq24819 eq24626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24626 eq24819
  have eq30818 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq30770
  have eq30837 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30818
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq30818
    | exact resolve eq30818 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30818
  have eq30847 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq30837
    | exact resolve eq30837 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30837
  have eq30887 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30847 eq24716
    | exact resolve eq24716 eq30847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24716 eq30847
  have eq30897 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30887
  have eq30965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30897 eq26087
    | exact resolve eq26087 eq30897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26087 eq30897
  have eq31002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30965
  have eq31028 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq31002
       have r₂ := eq29
       grind)
    | exact resolve eq31002 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31002
  have eq31047 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq31028 eq31
    | exact resolve eq31 eq31028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq31028
  have eq31165 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq31047
    | exact resolve eq31047 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31047
  have eq31166 : x = y := by grind
  clear eq31165
  have eq31314 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq31166
       grind)
    | exact superpose eq31166 eq20
    | exact resolve eq20 eq31166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq31315 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq31166
       grind)
    | exact superpose eq31166 eq26
    | exact resolve eq26 eq31166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq31166
  have eq31431 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31315
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31315
    | exact resolve eq31315 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31315
  have eq31447 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31431 eq28
    | exact resolve eq28 eq31431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq31431
  have eq31696 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31447 eq72
    | exact resolve eq72 eq31447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq31447
  have eq31764 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq31696
       have i₂ := eq31314
       grind)
    | exact superpose eq31314 eq31696
    | exact resolve eq31696 eq31314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31314 eq31696
  have eq31783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31764 eq15
    | exact resolve eq15 eq31764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31764
  have eq31832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq31783
    | exact resolve eq31783 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31783
  have eq31842 : False := by grind
  exact eq31842

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq30
  have eq49 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq22 (σ X0) (σ X0)
       grind)
    | exact superpose eq22 eq45
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq80 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq185 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq80 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq192 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq193 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq198 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq193
    | (have j0 := eq193 X0 X1
       grind)
    | exact resolve eq193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq715 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq199
    | exact resolve eq199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199 x y
       grind)
    | exact superpose eq199 eq16
    | (have j1 := eq199 x y
       grind)
    | exact resolve eq16 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq746 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq715
    | (have j0 := eq715 X0 X1
       grind)
    | exact resolve eq715 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq715
  have eq812 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq746 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq746
    | exact resolve eq746 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq875 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq812 (τ X0) X1
       grind)
    | exact superpose eq812 eq18
    | (have j1 := eq812 (τ X0) X1
       grind)
    | exact resolve eq18 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1386 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq875 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq875
    | exact resolve eq875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq1440 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1386 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1386
    | (have j0 := eq1386 X0 X1
       grind)
    | exact resolve eq1386 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1867 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq722
       have i₂ := eq1440 x y
       grind)
    | exact superpose eq1440 eq722
    | (have j1 := eq1440 (σ x) (σ y)
       grind)
    | (have r₁ := eq722
       have r₂ := eq1440 x y
       grind)
    | exact resolve eq722 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq1868 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1867
  have eq1892 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1868
  have eq1965 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq722
       have i₂ := eq1892
       grind)
    | exact superpose eq1892 eq722
    | exact resolve eq722 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq1892
  have eq1966 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1965
  have eq1967 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1966
  have eq2087 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq49 y
       have i₂ := eq1967
       grind)
    | exact superpose eq1967 eq49
    | exact resolve eq49 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2102 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22 (σ y) (σ y)
       have i₂ := eq1967
       grind)
    | exact superpose eq1967 eq22
    | exact resolve eq22 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq2126 : x = (k x y) := by
    first
    | (have i₁ := eq2087
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2087
    | exact resolve eq2087 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2138 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq812 x y
       have i₂ := eq2126
       grind)
    | exact superpose eq2126 eq812
    | (have j0 := eq812 x y
       grind)
    | exact resolve eq812 eq2126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq2126
  have eq2232 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2102
       grind)
    | exact superpose eq2102 eq16
    | exact resolve eq16 eq2102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq2523 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2232
       have i₂ := eq2138
       grind)
    | exact superpose eq2138 eq2232
    | exact resolve eq2232 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138
  have eq2549 : x = (M.op y y) := by grind
  clear eq2523
  have eq2564 : x = (M.op x y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq2549
       grind)
    | exact superpose eq2549 eq22
    | exact resolve eq22 eq2549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2549
  have eq2713 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2232
       have i₂ := eq2564
       grind)
    | exact superpose eq2564 eq2232
    | exact resolve eq2232 eq2564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232 eq2564
  have eq2739 : False := by grind
  exact eq2739

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq70 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq69 (τ X0)
       grind)
    | exact superpose eq69 eq19
    | exact resolve eq19 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq71 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq23
    | exact resolve eq23 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq407 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2650 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq407 X0 (τ X0)
       grind)
    | exact superpose eq407 eq70
    | (have j1 := eq407 X0 (τ X0)
       grind)
    | exact resolve eq70 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq407
  have eq2708 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq2650 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650
  have eq2711 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2708 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2708
    | (have j0 := eq2708 X0
       grind)
    | exact resolve eq2708 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2708
  have eq2736 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq2711 (σ X0)
       grind)
    | exact superpose eq2711 eq23
    | (have j1 := eq2711 (σ X0)
       grind)
    | exact resolve eq23 eq2711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2784 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2736 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq2736
    | (have j0 := eq2736 X0
       grind)
    | exact resolve eq2736 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736
  have eq2824 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2784 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2784
    | (have j0 := eq2784 X0
       grind)
    | exact resolve eq2784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq2860 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2824 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2824
    | (have j0 := eq2824 X0
       grind)
    | exact resolve eq2824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq2933 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq2860 (σ X0)
       grind)
    | exact superpose eq2860 eq23
    | (have j1 := eq2860 (σ X0)
       grind)
    | exact resolve eq23 eq2860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq2981 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2933 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq2933
    | (have j0 := eq2933 X0
       grind)
    | exact resolve eq2933 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2933
  have eq3021 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2981 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2981
    | (have j0 := eq2981 X0
       grind)
    | exact resolve eq2981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981
  have eq5622 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq384
    | (have j0 := eq384 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq384 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5625 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq384 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq384
    | (have j0 := eq384 (M.op X0 X0) X0
       grind)
    | exact resolve eq384 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5665 : ∀ X0 X1 X2 : G, (σ (k (k X0 X1) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 X1) X2
       have i₂ := eq384 X0 X1
       grind)
    | exact superpose eq384 eq15
    | (have j1 := eq384 X0 X1
       grind)
    | exact resolve eq15 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32624 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69 (σ X0)
       have i₂ := eq5665 X0 X0 X0
       grind)
    | exact superpose eq5665 eq69
    | (have j1 := eq5665 X0 X0 x
       grind)
    | exact resolve eq69 eq5665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq5665
  have eq32643 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32624 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32624
  have eq32661 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq3021 eq32643
    | (have j0 := eq32643 X0
       have j1 := eq3021 X0
       grind)
    | exact resolve eq32643 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021 eq32643
  have eq32697 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32661 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq32661
    | (have j0 := eq32661 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq32661 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32661
  have eq32800 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq32697 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32697
  have eq35288 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq32800 X0
       grind)
    | exact superpose eq32800 eq64
    | (have j1 := eq32800 X0
       grind)
    | exact resolve eq64 eq32800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32800
  have eq48787 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5622 x y
       grind)
    | exact superpose eq5622 eq16
    | (have j1 := eq5622 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq5622 x y
       grind)
    | exact resolve eq16 eq5622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5622
  have eq48925 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq48787
  have eq87081 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48925
       grind)
    | exact superpose eq48925 eq16
    | exact resolve eq16 eq48925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87086 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq48925
       grind)
    | exact superpose eq48925 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq48925
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq48925
       grind)
    | exact resolve eq13 eq48925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48925
  have eq87179 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq87086
  have eq87180 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq87179
  have eq87198 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq87180
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq87180
    | exact resolve eq87180 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87180
  have eq87203 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq87198
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq87198 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87198
  have eq87207 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq87203
       have r₂ := eq87081
       grind)
    | exact resolve eq87203 eq87081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87081 eq87203
  have eq87212 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71 y
       have i₂ := eq87207
       grind)
    | exact superpose eq87207 eq71
    | exact resolve eq71 eq87207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87265 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64 (σ y) (σ y)
       have i₂ := eq87207
       grind)
    | exact superpose eq87207 eq64
    | exact resolve eq64 eq87207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87207
  have eq87395 : y = (M.op x y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq87212
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq87212
    | exact resolve eq87212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87212
  have eq87432 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq87395
       grind)
    | exact superpose eq87395 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq87395
       grind)
    | exact resolve eq13 eq87395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87395
  have eq87525 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) ∨ x = (k x y) := by grind
  clear eq87432
  have eq87526 : y = (k x y) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq87525
  have eq87722 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq87526
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq87526
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq87526 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87526
  have eq87728 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq87722
  have eq89923 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq87265
       grind)
    | exact superpose eq87265 eq16
    | exact resolve eq16 eq87265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87265
  have eq90058 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87728 eq89923
    | exact resolve eq89923 eq87728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87728 eq89923
  have eq90059 : y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq90058
  have eq90103 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq90059
       grind)
    | exact superpose eq90059 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq90059
       grind)
    | exact resolve eq13 eq90059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90107 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64 y x
       have i₂ := eq90059
       grind)
    | exact superpose eq90059 eq64
    | exact resolve eq64 eq90059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90196 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) := by grind
  clear eq90103
  have eq90197 : y = (k x y) ∨ x = (M.op y y) := by grind
  clear eq90196
  have eq90339 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq90107
  have eq90400 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq384 x y
       have i₂ := eq90197
       grind)
    | exact superpose eq90197 eq384
    | (have j0 := eq384 x y
       grind)
    | exact resolve eq384 eq90197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq90403 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq90400
  have eq106507 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq90403
       grind)
    | exact superpose eq90403 eq16
    | exact resolve eq16 eq90403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90403
  have eq106700 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq90059 eq106507
    | exact resolve eq106507 eq90059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90059 eq106507
  have eq106701 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq106700
  have eq106821 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71 y
       have i₂ := eq106701
       grind)
    | exact superpose eq106701 eq71
    | exact resolve eq71 eq106701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106701
  have eq107025 : x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq106821
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq106821
    | exact resolve eq106821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106821
  have eq107377 : x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq107025 eq90197
    | exact resolve eq90197 eq107025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90197 eq107025
  have eq107384 : x = (M.op y y) := by
    first
    | (have r₁ := eq107377
       have r₂ := eq90339
       grind)
    | exact resolve eq107377 eq90339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90339 eq107377
  have eq107412 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq35288 y
       have i₂ := eq107384
       grind)
    | exact superpose eq107384 eq35288
    | (have j0 := eq35288 y
       grind)
    | exact resolve eq35288 eq107384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35288
  have eq107427 : x = (M.op x y) := by
    first
    | (have i₁ := eq64 y y
       have i₂ := eq107384
       grind)
    | exact superpose eq107384 eq64
    | exact resolve eq64 eq107384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq107522 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107427
       grind)
    | exact superpose eq107427 eq16
    | exact resolve eq16 eq107427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107427
  have eq110223 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq107522
       have r₂ := eq107412
       grind)
    | exact resolve eq107522 eq107412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107412
  have eq110226 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = y := by
    first
    | (have i₁ := eq71 y
       have i₂ := eq110223
       grind)
    | exact superpose eq110223 eq71
    | exact resolve eq71 eq110223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq110223
  have eq110399 : y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq110226
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq110226
    | exact resolve eq110226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110226
  have eq110440 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq110399
       grind)
    | exact superpose eq110399 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq110399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110399
  have eq110441 : y = (M.op y y) ∨ x = y := by grind
  clear eq110440
  have eq110455 : x = y ∨ x = y := by
    first
    | (have i₁ := eq110441
       have i₂ := eq107384
       grind)
    | exact superpose eq107384 eq110441
    | exact resolve eq110441 eq107384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110441
  have eq110456 : x = y := by grind
  clear eq110455
  have eq110470 : x = (M.op x x) := by
    first
    | (have i₁ := eq107384
       have i₂ := eq110456
       grind)
    | exact superpose eq110456 eq107384
    | exact resolve eq107384 eq110456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107384
  have eq110484 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq107522
       have i₂ := eq110456
       grind)
    | exact superpose eq110456 eq107522
    | exact resolve eq107522 eq110456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107522 eq110456
  have eq110497 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5625 x
       have i₂ := eq110470
       grind)
    | exact superpose eq110470 eq5625
    | exact resolve eq5625 eq110470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5625 eq110470
  have eq110612 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq110497
  have eq110654 : False := by grind
  exact eq110654

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pxx_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq278 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq16
    | (have j1 := eq88 x y
       grind)
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq278
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq278
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq278
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq278
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq1198 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq1197
  have eq2988 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq3018 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq81 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq3019 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2988 X0
       have i₂ := eq41 X0 X0
       grind)
    | exact superpose eq41 eq2988
    | (have j0 := eq2988 X0
       grind)
    | exact resolve eq2988 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2988
  have eq3024 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3019 X0
       have j1 := eq3018 X0
       grind)
    | (have r₁ := eq3019 X0
       have r₂ := eq3018 X0
       grind)
    | exact resolve eq3019 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018 eq3019
  have eq3028 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3024 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3024
    | exact resolve eq3024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3024
  have eq3085 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq3028 X0
       have i₂ := eq24 (σ X0) X0
       grind)
    | exact superpose eq24 eq3028
    | exact resolve eq3028 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3028
  have eq3090 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3085 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3085
    | exact resolve eq3085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085
  have eq3266 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3090 (σ X0)
       grind)
    | exact superpose eq3090 eq15
    | exact resolve eq15 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3284 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3266 X0
       have i₂ := eq3090 X0
       grind)
    | exact superpose eq3090 eq3266
    | exact resolve eq3266 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3090 eq3266
  have eq3620 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq36 (σ X0) (σ X0)
       have i₂ := eq3284 X0
       grind)
    | exact superpose eq3284 eq36
    | exact resolve eq36 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25779 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1198
       grind)
    | exact superpose eq1198 eq16
    | exact resolve eq16 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq25780 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq25779
       have r₂ := eq3284 x
       grind)
    | exact resolve eq25779 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25779
  have eq25781 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25780
       have i₂ := eq3284 y
       grind)
    | exact superpose eq3284 eq25780
    | exact resolve eq25780 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25780
  have eq25783 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25781
       grind)
    | exact superpose eq25781 eq10
    | exact resolve eq10 eq25781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25781
  have eq25870 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25783
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25783
    | exact resolve eq25783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25783
  have eq25884 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25870
       grind)
    | exact superpose eq25870 eq16
    | exact resolve eq16 eq25870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25870
  have eq25885 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq25884
       have r₂ := eq3284 x
       grind)
    | exact resolve eq25884 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284 eq25884
  have eq26160 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq25885
       grind)
    | exact superpose eq25885 eq10
    | exact resolve eq10 eq25885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25885
  have eq26248 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq26160
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26160
    | exact resolve eq26160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26160
  have eq26249 : x = (M.op y y) := by grind
  clear eq26248
  have eq26280 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3620 y
       have i₂ := eq26249
       grind)
    | exact superpose eq26249 eq3620
    | exact resolve eq3620 eq26249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620
  have eq26305 : x = (M.op x y) := by
    first
    | (have i₁ := eq36 y y
       have i₂ := eq26249
       grind)
    | exact superpose eq26249 eq36
    | exact resolve eq36 eq26249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq26249
  have eq27202 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26280
       grind)
    | exact superpose eq26280 eq16
    | exact resolve eq16 eq26280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26280
  have eq27286 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq27202
       have i₂ := eq26305
       grind)
    | exact superpose eq26305 eq27202
    | exact resolve eq27202 eq26305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26305 eq27202
  have eq27287 : False := by grind
  exact eq27287

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation442 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq203 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1261 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq203 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq203
    | exact resolve eq203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq1328 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1261 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1261
    | (have j0 := eq1261 X0 X1
       grind)
    | exact resolve eq1261 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq2667 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq16
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2681 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq17151 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2667
       have i₂ := eq1328 x y
       grind)
    | exact superpose eq1328 eq2667
    | (have j1 := eq1328 (σ x) (σ y)
       grind)
    | (have r₁ := eq2667
       have r₂ := eq1328 x y
       grind)
    | (have r₁ := eq2667
       have r₂ := eq1328 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2667
       have r₂ := eq1328 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2667 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq17152 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17151
  have eq17609 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17152
       grind)
    | exact superpose eq17152 eq16
    | exact resolve eq16 eq17152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17152
  have eq17610 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17609
       have r₂ := eq22 x
       grind)
    | exact resolve eq17609 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17609
  have eq17612 : y ≠ y ∨ x = y ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq17610
       grind)
    | exact superpose eq17610 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17610
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17610
       grind)
    | exact resolve eq13 eq17610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17616 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq110 y x
       have i₂ := eq17610
       grind)
    | exact superpose eq17610 eq110
    | exact resolve eq110 eq17610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17610
  have eq17622 : (k x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17612
  have eq17632 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq110 (σ y) (σ x)
       have i₂ := eq17616
       grind)
    | exact superpose eq17616 eq110
    | exact resolve eq110 eq17616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq17616
  have eq17644 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17632
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq17632
    | exact resolve eq17632 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17632
  have eq17655 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17644
       grind)
    | exact superpose eq17644 eq10
    | exact resolve eq10 eq17644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17644
  have eq17716 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17655
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17655
    | exact resolve eq17655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17655
  have eq17718 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17716
       grind)
    | exact superpose eq17716 eq16
    | exact resolve eq16 eq17716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17716
  have eq17719 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq17718
       have r₂ := eq22 x
       grind)
    | exact resolve eq17718 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17718
  have eq17733 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq17719
       grind)
    | exact superpose eq17719 eq10
    | exact resolve eq10 eq17719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17719
  have eq17794 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17733
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq17733
    | exact resolve eq17733 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17733
  have eq17795 : y = (M.op y y) := by grind
  clear eq17794
  have eq429693 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2681 x y
       have i₂ := eq17622
       grind)
    | exact superpose eq17622 eq2681
    | (have j0 := eq2681 x y
       grind)
    | exact resolve eq2681 eq17622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2681 eq17622
  have eq429742 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq429693
  have eq429809 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq429742
       have i₂ := eq17795
       grind)
    | exact superpose eq17795 eq429742
    | exact resolve eq429742 eq17795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429742
  have eq429810 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq429809
  have eq429922 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq429810
       grind)
    | exact superpose eq429810 eq10
    | exact resolve eq10 eq429810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429810
  have eq430113 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq429922
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq429922
    | exact resolve eq429922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429922
  have eq430114 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq430113
  have eq430127 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq430114
       grind)
    | exact superpose eq430114 eq16
    | exact resolve eq16 eq430114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430205 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq430114
       grind)
    | exact superpose eq430114 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq430114
       grind)
    | exact resolve eq13 eq430114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430114
  have eq430326 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq430205
  have eq430385 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq430326
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq430326
    | exact resolve eq430326 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430326
  have eq430458 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq430385
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq430385
    | exact resolve eq430385 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430385
  have eq430480 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq430458
       have i₂ := eq17795
       grind)
    | exact superpose eq17795 eq430458
    | exact resolve eq430458 eq17795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17795 eq430458
  have eq431854 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1328 x y
       have i₂ := eq430480
       grind)
    | exact superpose eq430480 eq1328
    | (have j0 := eq1328 x y
       grind)
    | exact resolve eq1328 eq430480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq430480
  have eq432003 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq431854
  have eq432040 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq432003
       have r₂ := eq430127
       grind)
    | exact resolve eq432003 eq430127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432003
  have eq432335 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq432040
       grind)
    | exact superpose eq432040 eq10
    | exact resolve eq10 eq432040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432040
  have eq432531 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq432335
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq432335
    | exact resolve eq432335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432335
  have eq432532 : y = (M.op x y) ∨ x = y := by grind
  clear eq432531
  have eq432541 : (σ y) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq430127
       have i₂ := eq432532
       grind)
    | exact superpose eq432532 eq430127
    | exact resolve eq430127 eq432532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430127 eq432532
  have eq432830 : (σ y) ≠ (σ y) ∨ x = y := by grind
  clear eq432541
  have eq432831 : x = y := by grind
  clear eq432830
  have eq432869 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq432831
       grind)
    | exact superpose eq432831 eq16
    | exact resolve eq16 eq432831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432831
  have eq433391 : False := by grind
  exact eq433391

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation442 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law442 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq582 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq611 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq620 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq603
    | (have j0 := eq603 X0 X1
       grind)
    | exact resolve eq603 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq3408 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq620 x y
       grind)
    | exact superpose eq620 eq16
    | (have j1 := eq620 x y
       grind)
    | exact resolve eq16 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3422 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq4500 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq611 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq611
    | exact resolve eq611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq4564 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4500 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4500
    | (have j0 := eq4500 X0 X1
       grind)
    | exact resolve eq4500 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4500
  have eq13489 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3408
       have i₂ := eq4564 y x
       grind)
    | exact superpose eq4564 eq3408
    | (have j1 := eq4564 y x
       grind)
    | (have r₁ := eq3408
       have r₂ := eq4564 y x
       grind)
    | (have r₁ := eq3408
       have r₂ := eq4564 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3408
       have r₂ := eq4564 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3408 eq4564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3408 eq4564
  have eq13490 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq13489
  have eq20644 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3422 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3422
    | (have j0 := eq3422 (τ X1) (τ X0)
       grind)
    | exact resolve eq3422 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq20700 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20644 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq20644
    | (have j0 := eq20644 X0 X1
       grind)
    | exact resolve eq20644 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20644
  have eq20732 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20700 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq20700
    | (have j0 := eq20700 X0 X1
       grind)
    | exact resolve eq20700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20700
  have eq20761 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20732 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20732
    | (have j0 := eq20732 X0 X1
       grind)
    | exact resolve eq20732 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20732
  have eq20786 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20761 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20761
    | (have j0 := eq20761 X0 X1
       grind)
    | exact resolve eq20761 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20761
  have eq20805 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20786 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq20786
    | (have j0 := eq20786 X0 X1
       grind)
    | exact resolve eq20786 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20786
  have eq20823 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20805 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20805
    | (have j0 := eq20805 X0 X1
       grind)
    | exact resolve eq20805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20805
  have eq20836 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20823 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20823
    | (have j0 := eq20823 X0 X1
       grind)
    | exact resolve eq20823 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20823
  have eq54191 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13490
       grind)
    | exact superpose eq13490 eq16
    | exact resolve eq16 eq13490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13490
  have eq54192 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq54191
       have r₂ := eq22 x
       grind)
    | exact resolve eq54191 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54191
  have eq54194 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq54192
       grind)
    | exact superpose eq54192 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq54192
       grind)
    | exact resolve eq13 eq54192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54192
  have eq54266 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq54194
  have eq82043 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54266
       grind)
    | exact superpose eq54266 eq16
    | exact resolve eq16 eq54266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54266
  have eq82044 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq82043
       have r₂ := eq22 x
       grind)
    | exact resolve eq82043 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82043
  have eq82050 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3422 x y
       have i₂ := eq82044
       grind)
    | exact superpose eq82044 eq3422
    | (have j0 := eq3422 x y
       grind)
    | exact resolve eq3422 eq82044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422 eq82044
  have eq82082 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq82050
  have eq82083 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq82082
  have eq82090 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82083
       grind)
    | exact superpose eq82083 eq16
    | exact resolve eq16 eq82083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82091 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq582 x (σ y)
       have i₂ := eq82083
       grind)
    | exact superpose eq82083 eq582
    | (have j0 := eq582 x (σ y)
       grind)
    | (have r₁ := eq582 x (σ y)
       have r₂ := eq82083
       grind)
    | exact resolve eq582 eq82083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq82083
  have eq82204 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq82091
  have eq82205 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq82204
  have eq82246 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq82205
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq82205
    | exact resolve eq82205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82205
  have eq82253 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq82246
       grind)
    | exact superpose eq82246 eq10
    | exact resolve eq10 eq82246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82246
  have eq82464 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq82253
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq82253
    | exact resolve eq82253 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82253
  have eq82466 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82464
       grind)
    | exact superpose eq82464 eq16
    | exact resolve eq16 eq82464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82464
  have eq82467 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq82466
       have r₂ := eq22 x
       grind)
    | exact resolve eq82466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82466
  have eq82482 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq82467
       grind)
    | exact superpose eq82467 eq10
    | exact resolve eq10 eq82467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82467
  have eq82694 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq82482
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq82482
    | exact resolve eq82482 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82482
  have eq82723 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq20836 y x
       have i₂ := eq82694
       grind)
    | exact superpose eq82694 eq20836
    | (have j0 := eq20836 y x
       grind)
    | (have r₁ := eq20836 y x
       have r₂ := eq82694
       grind)
    | exact resolve eq20836 eq82694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20836 eq82694
  have eq82734 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq82723
  have eq82738 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82734
       grind)
    | exact superpose eq82734 eq16
    | exact resolve eq16 eq82734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82734
  have eq82741 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq82738
       have r₂ := eq22 x
       grind)
    | exact resolve eq82738 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82738
  have eq82742 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq82090
       have i₂ := eq82741
       grind)
    | exact superpose eq82741 eq82090
    | exact resolve eq82090 eq82741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82090
  have eq82833 : (σ x) = (σ y) := by grind
  clear eq82742
  have eq82834 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82833
       grind)
    | exact superpose eq82833 eq16
    | exact resolve eq16 eq82833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82833
  have eq83047 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq82834
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq82834
    | exact resolve eq82834 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq82834
  have eq83048 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq83047
       have i₂ := eq82741
       grind)
    | exact superpose eq82741 eq83047
    | exact resolve eq83047 eq82741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82741 eq83047
  have eq83049 : False := by grind
  exact eq83049

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation442 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law442 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1261 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq200 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq200
    | exact resolve eq200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq1328 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1261 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1261
    | (have j0 := eq1261 X0 X1
       grind)
    | exact resolve eq1261 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq2719 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq16
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2733 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq17189 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2719
       have i₂ := eq1328 x y
       grind)
    | exact superpose eq1328 eq2719
    | (have j1 := eq1328 (σ x) (σ y)
       grind)
    | (have r₁ := eq2719
       have r₂ := eq1328 x y
       grind)
    | (have r₁ := eq2719
       have r₂ := eq1328 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2719
       have r₂ := eq1328 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2719 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2719
  have eq17190 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17189
  have eq17647 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17190
       grind)
    | exact superpose eq17190 eq16
    | exact resolve eq16 eq17190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17190
  have eq17648 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17647
       have r₂ := eq22 x
       grind)
    | exact resolve eq17647 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17647
  have eq17650 : y ≠ y ∨ x = y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq17648
       grind)
    | exact superpose eq17648 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17648
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17648
       grind)
    | exact resolve eq13 eq17648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17654 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq110 y x
       have i₂ := eq17648
       grind)
    | exact superpose eq17648 eq110
    | exact resolve eq110 eq17648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17648
  have eq17660 : (k y x) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17650
  have eq17670 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq110 (σ y) (σ x)
       have i₂ := eq17654
       grind)
    | exact superpose eq17654 eq110
    | exact resolve eq110 eq17654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq17654
  have eq17682 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17670
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq17670
    | exact resolve eq17670 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17670
  have eq17693 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17682
       grind)
    | exact superpose eq17682 eq10
    | exact resolve eq10 eq17682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17682
  have eq17754 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17693
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17693
    | exact resolve eq17693 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17693
  have eq17756 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17754
       grind)
    | exact superpose eq17754 eq16
    | exact resolve eq16 eq17754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17754
  have eq17757 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq17756
       have r₂ := eq22 x
       grind)
    | exact resolve eq17756 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17756
  have eq17771 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq17757
       grind)
    | exact superpose eq17757 eq10
    | exact resolve eq10 eq17757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17757
  have eq17832 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17771
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq17771
    | exact resolve eq17771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17771
  have eq17833 : y = (M.op y y) := by grind
  clear eq17832
  have eq431635 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2733 x y
       have i₂ := eq17660
       grind)
    | exact superpose eq17660 eq2733
    | (have j0 := eq2733 x y
       grind)
    | exact resolve eq2733 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733 eq17660
  have eq431684 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq431635
  have eq431751 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq431684
       have i₂ := eq17833
       grind)
    | exact superpose eq17833 eq431684
    | exact resolve eq431684 eq17833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431684
  have eq431752 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq431751
  have eq431864 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq431752
       grind)
    | exact superpose eq431752 eq10
    | exact resolve eq10 eq431752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431752
  have eq432055 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq431864
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq431864
    | exact resolve eq431864 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431864
  have eq432056 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq432055
  have eq433523 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq432056
       grind)
    | exact superpose eq432056 eq16
    | exact resolve eq16 eq432056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433601 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq432056
       grind)
    | exact superpose eq432056 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq432056
       grind)
    | exact resolve eq13 eq432056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432056
  have eq433723 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq433601
  have eq433783 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq433723
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq433723
    | exact resolve eq433723 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433723
  have eq433857 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq433783
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq433783
    | exact resolve eq433783 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433783
  have eq433879 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq433857
       have i₂ := eq17833
       grind)
    | exact superpose eq17833 eq433857
    | exact resolve eq433857 eq17833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17833 eq433857
  have eq433902 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1328 x y
       have i₂ := eq433879
       grind)
    | exact superpose eq433879 eq1328
    | (have j0 := eq1328 x y
       grind)
    | exact resolve eq1328 eq433879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq433879
  have eq434051 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq433902
  have eq434088 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq434051
       have r₂ := eq433523
       grind)
    | exact resolve eq434051 eq433523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434051
  have eq434383 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq434088
       grind)
    | exact superpose eq434088 eq10
    | exact resolve eq10 eq434088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434088
  have eq434579 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq434383
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq434383
    | exact resolve eq434383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434383
  have eq434580 : y = (M.op x y) ∨ x = y := by grind
  clear eq434579
  have eq434589 : (σ y) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq433523
       have i₂ := eq434580
       grind)
    | exact superpose eq434580 eq433523
    | exact resolve eq433523 eq434580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433523 eq434580
  have eq434879 : (σ y) ≠ (σ y) ∨ x = y := by grind
  clear eq434589
  have eq434880 : x = y := by grind
  clear eq434879
  have eq434919 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq434880
       grind)
    | exact superpose eq434880 eq16
    | exact resolve eq16 eq434880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434880
  have eq435441 : False := by grind
  exact eq435441

/-- `Equation4425`: `x ◇ (x ◇ y) = (z ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_pxx_x_pxy_Equation4425 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4425 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4425.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X2) := by
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
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X3 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ (M.op x x)) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq35 (M.op x x)
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq35
    | exact resolve eq35 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq182 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq178 sF2
       grind)
    | exact superpose eq178 eq90
    | exact resolve eq90 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq193 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq178 sF3
       grind)
    | exact superpose eq178 eq107
    | exact resolve eq107 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq560 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 X2 X3 X4 (M.op X4 x)
       have i₂ := eq177 X4 x X0 X1
       grind)
    | (have i₁ := eq177 X2 X3 X4 (M.op X4 x)
       have i₂ := eq177 X0 X1 X4 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X3 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X1 X2 X3 (M.op X3 x)
       have i₂ := eq16 X3 x X0
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 X1 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X4) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq177 X2 x X0 X1
       grind)
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq177 X0 X1 X2 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq565 x x
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq565 (σ x) (σ y)
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq565
    | (have j0 := eq565 (σ x) (σ y)
       have j1 := eq566 x y
       grind)
    | exact resolve eq565 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq578 : ∀ X0 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X3 (M.op (M.op X0 X0) X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq561 X0 x x X3
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq561 X0 (σ x) (σ y) X3
       have i₂ := eq566 X0 x
       grind)
    | exact superpose eq566 eq561
    | (have j0 := eq561 X0 (σ x) (σ y) X3
       grind)
    | exact resolve eq561 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq579 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq560 x x X2 X3 X4
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq560 (σ x) (σ y) X2 X3 X4
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq560
    | (have j0 := eq560 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq560 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq589 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq579 x x X4
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq579 (σ x) (σ y) X4
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq579
    | (have j0 := eq579 (σ x) (σ y) X4
       grind)
    | exact resolve eq579 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq612 : ∀ X2 : G, (M.op (M.op X2 X2) X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | (have i₁ := eq16 x x X2
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq16 (σ x) (σ y) X2
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq16
    | (have j0 := eq16 (σ x) (σ y) X2
       grind)
    | exact resolve eq16 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq589 eq178
    | exact resolve eq178 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq918 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq925 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq926 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq925 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq983 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq926 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq926
    | (have j0 := eq926 (σ X0)
       grind)
    | exact resolve eq926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2444 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq912
       grind)
    | exact superpose eq912 eq40
    | exact resolve eq40 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2445 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2444
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2444
    | exact resolve eq2444 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2444
  have eq2447 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2445
    | exact resolve eq2445 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2445
  have eq15919 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) ≠ (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq635 eq983
    | (have j0 := eq983 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq983 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15955 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by grind
  clear eq15919
  have eq16126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2447 eq918
    | exact resolve eq918 eq2447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16133 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16126
       have r₂ := eq27
       grind)
    | exact resolve eq16126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16126
  have eq16140 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16133 eq193
    | exact resolve eq193 eq16133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16133
  have eq16173 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq16140
    | exact resolve eq16140 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16140
  have eq16184 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq926 y
       grind)
    | (have r₁ := eq16173
       have r₂ := eq926 y
       grind)
    | exact resolve eq16173 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16173
  have eq16189 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16184 eq182
    | exact resolve eq182 eq16184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq16203 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16184 eq178
    | exact resolve eq178 eq16184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16184
  have eq16223 : y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq16189
    | exact resolve eq16189 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16189
  have eq16229 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq912 eq16223
    | exact resolve eq16223 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912 eq16223
  have eq16246 : y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq16229
       grind)
    | exact superpose eq16229 eq178
    | exact resolve eq178 eq16229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16249 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq578 y X0
       have i₂ := eq16229
       grind)
    | exact superpose eq16229 eq578
    | exact resolve eq578 eq16229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16251 : (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq612 y
       have i₂ := eq16229
       grind)
    | exact superpose eq16229 eq612
    | exact resolve eq612 eq16229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16254 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16229 eq16251
    | exact resolve eq16251 eq16229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16251
  have eq16255 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq16229 eq16249
    | exact resolve eq16249 eq16229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16229 eq16249
  have eq16267 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq16254 eq16255
    | exact resolve eq16255 eq16254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16255
  have eq16285 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq983 y
       have i₂ := eq16246
       grind)
    | exact superpose eq16246 eq983
    | (have j0 := eq983 y
       grind)
    | exact resolve eq983 eq16246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16246
  have eq16293 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq16285
  have eq16294 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16293
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16293
    | exact resolve eq16293 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16293
  have eq16350 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq566 x x
       have i₂ := eq16267 X0
       grind)
    | exact superpose eq16267 eq566
    | (have j1 := eq16267 x
       grind)
    | exact resolve eq566 eq16267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16267
  have eq16374 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16350 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16350
    | (have j0 := eq16350 x
       grind)
    | exact resolve eq16350 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16350
  have eq16404 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq16294 eq578
    | exact resolve eq578 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16406 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16294 eq612
    | exact resolve eq612 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16409 : y = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16254 eq16406
    | exact resolve eq16406 eq16254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16406
  have eq16410 : ∀ X0 : G, y = (M.op X0 (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq16254 eq16404
    | exact resolve eq16404 eq16254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16254 eq16404
  have eq16422 : y = (M.op x x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq16294 eq16409
    | exact resolve eq16409 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16409
  have eq16423 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq16294 eq16410
    | exact resolve eq16410 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16294 eq16410
  have eq16434 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq16422 eq16423
    | exact resolve eq16423 eq16422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16423
  have eq16453 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq566 x x
       have i₂ := eq16422
       grind)
    | exact superpose eq16422 eq566
    | exact resolve eq566 eq16422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16422
  have eq16477 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq16453
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16453
    | exact resolve eq16453 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16453
  have eq16510 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq16477 eq15955
    | exact resolve eq15955 eq16477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16524 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq16510
    | exact resolve eq16510 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16510
  have eq16680 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq16524 eq566
    | exact resolve eq566 eq16524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16685 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq16477 eq16680
    | exact resolve eq16680 eq16477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16680
  have eq16753 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq16685 eq16524
    | exact resolve eq16524 eq16685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16685
  have eq16775 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq16753
  have eq16803 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq16775 eq28
    | exact resolve eq28 eq16775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq17520 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq16374 eq15955
    | (have j1 := eq16374 x
       grind)
    | exact resolve eq15955 eq16374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16374
  have eq17535 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq20 eq17520
    | (have j0 := eq17520 x
       grind)
    | exact resolve eq17520 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17520
  have eq17544 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq16524 eq17535
    | (have j0 := eq17535 x
       grind)
    | exact resolve eq17535 eq16524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16524 eq17535
  have eq17717 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16434 eq26
    | (have j1 := eq16434 (σ x)
       grind)
    | exact resolve eq26 eq16434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16434
  have eq17783 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179
       have i₂ := eq17717
       grind)
    | exact superpose eq17717 eq179
    | exact resolve eq179 eq17717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq17801 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq566 x x
       have i₂ := eq17717
       grind)
    | exact superpose eq17717 eq566
    | exact resolve eq566 eq17717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17802 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq573 x x X1 X0
       have i₂ := eq17717
       grind)
    | exact superpose eq17717 eq573
    | exact resolve eq573 eq17717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq17717
  have eq17805 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq17802 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17802
    | (have j0 := eq17802 X0 X1
       grind)
    | exact resolve eq17802 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq17806 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17801
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17801
    | exact resolve eq17801 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17801
  have eq17817 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17783
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17783
    | exact resolve eq17783 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17783
  have eq17818 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq17805 x X1
       have i₂ := eq612 x
       grind)
    | exact superpose eq612 eq17805
    | exact resolve eq17805 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq17805
  have eq17823 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq17806 eq17818
    | exact resolve eq17818 eq17806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17818
  have eq17847 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17806 eq15955
    | exact resolve eq15955 eq17806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17861 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17847
    | exact resolve eq17847 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17847
  have eq17873 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17817 eq918
    | exact resolve eq918 eq17817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq17817
  have eq17877 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq17873
  have eq18012 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17861 eq566
    | exact resolve eq566 eq17861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18022 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17806 eq18012
    | exact resolve eq18012 eq17806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18012
  have eq18077 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18022 eq17861
    | exact resolve eq17861 eq18022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17861 eq18022
  have eq18101 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq18077
  have eq18133 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq18101 eq589
    | exact resolve eq589 eq18101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq18134 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq18101 eq635
    | exact resolve eq635 eq18101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq18149 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26 eq18134
    | exact resolve eq18134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18134
  have eq18150 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26 eq18133
    | (have j0 := eq18133 X0
       grind)
    | exact resolve eq18133 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18133
  have eq18157 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq18101 eq18149
    | exact resolve eq18149 eq18101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18149
  have eq18158 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq18101 eq18150
    | exact resolve eq18150 eq18101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18101 eq18150
  have eq18531 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17544 eq178
    | exact resolve eq178 eq17544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17544
  have eq18572 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18157 eq18531
    | exact resolve eq18531 eq18157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18157 eq18531
  have eq19270 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18572 eq926
    | (have j0 := eq926 (σ y)
       grind)
    | (have r₁ := eq926 (σ y)
       have r₂ := eq18572
       grind)
    | exact resolve eq926 eq18572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926 eq18572
  have eq19281 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq19270
  have eq19476 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19281 eq578
    | exact resolve eq578 eq19281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19492 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19281 eq19476
    | exact resolve eq19476 eq19281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19281 eq19476
  have eq19505 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17823 eq19492
    | (have j1 := eq17823 (M.op x y)
       grind)
    | exact resolve eq19492 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19492
  have eq19518 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26 eq19505
    | (have j0 := eq19505 X0
       grind)
    | exact resolve eq19505 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19505
  have eq19528 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17823 eq19518
    | (have j1 := eq17823 (M.op x y)
       grind)
    | exact resolve eq19518 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17823 eq19518
  have eq20968 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16203 eq2447
    | exact resolve eq2447 eq16203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447 eq16203
  have eq20971 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq20968
  have eq20993 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq20971
       grind)
    | exact superpose eq20971 eq178
    | exact resolve eq178 eq20971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq21002 : (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq566 y y
       have i₂ := eq20971
       grind)
    | exact superpose eq20971 eq566
    | exact resolve eq566 eq20971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21007 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20971 eq21002
    | exact resolve eq21002 eq20971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20971 eq21002
  have eq21042 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq983 y
       have i₂ := eq20993
       grind)
    | exact superpose eq20993 eq983
    | (have j0 := eq983 y
       grind)
    | exact resolve eq983 eq20993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20993
  have eq21046 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq21042
  have eq21051 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21046
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21046
    | exact resolve eq21046 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21046
  have eq21178 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21051 eq578
    | exact resolve eq578 eq21051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21184 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21051 eq566
    | exact resolve eq566 eq21051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21189 : y = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21007 eq21184
    | exact resolve eq21184 eq21007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21184
  have eq21194 : ∀ X0 : G, y = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21007 eq21178
    | exact resolve eq21178 eq21007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21007 eq21178
  have eq21202 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq21051 eq21189
    | exact resolve eq21189 eq21051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21189
  have eq21207 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21051 eq21194
    | exact resolve eq21194 eq21051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21051 eq21194
  have eq21217 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21202 eq21207
    | exact resolve eq21207 eq21202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21202 eq21207
  have eq22277 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21217 eq26
    | (have j1 := eq21217 (σ x)
       grind)
    | exact resolve eq26 eq21217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21217
  have eq22361 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq566 x x
       have i₂ := eq22277
       grind)
    | exact superpose eq22277 eq566
    | exact resolve eq566 eq22277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22277
  have eq22366 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22361
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22361
    | exact resolve eq22361 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22361
  have eq22406 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22366 eq15955
    | exact resolve eq15955 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22423 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22406
    | exact resolve eq22406 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22406
  have eq22583 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22423 eq566
    | exact resolve eq566 eq22423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22596 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22366 eq22583
    | exact resolve eq22583 eq22366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22366 eq22583
  have eq22663 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22596 eq22423
    | exact resolve eq22423 eq22596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22423 eq22596
  have eq22684 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq22663
  have eq22723 : (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq22684 eq15955
    | exact resolve eq15955 eq22684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22737 : (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26 eq22723
    | exact resolve eq22723 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22723
  have eq22748 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq22684 eq22737
    | exact resolve eq22737 eq22684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22737
  have eq24520 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ (σ y)) (σ (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22748 eq578
    | exact resolve eq578 eq22748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq24543 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ (σ y)) (σ (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22684 eq24520
    | exact resolve eq24520 eq22684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24520
  have eq24560 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ (σ y)) (σ (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26 eq24543
    | (have j0 := eq24543 X0
       grind)
    | exact resolve eq24543 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24543
  have eq24575 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ (σ y)) (σ (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22684 eq24560
    | exact resolve eq24560 eq22684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22684 eq24560
  have eq24588 : ∀ X0 : G, (σ y) = (M.op X0 (σ (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22748 eq24575
    | exact resolve eq24575 eq22748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24575
  have eq24643 : (σ y) = (σ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq24588 eq22748
    | exact resolve eq22748 eq24588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22748 eq24588
  have eq24647 : (σ y) = (σ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq24643
  have eq30894 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17877 eq193
    | exact resolve eq193 eq17877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq30911 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17877 eq566
    | exact resolve eq566 eq17877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17877
  have eq30916 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17806 eq30911
    | exact resolve eq30911 eq17806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30911
  have eq30927 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq30894
    | exact resolve eq30894 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30894
  have eq33978 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30916 eq566
    | exact resolve eq566 eq30916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30916
  have eq33989 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq33978
    | exact resolve eq33978 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33978
  have eq34002 : (M.op x y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17806 eq33989
    | exact resolve eq33989 eq17806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33989
  have eq34318 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30927 eq566
    | exact resolve eq566 eq30927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30927
  have eq34329 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq34318
    | exact resolve eq34318 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34318
  have eq34342 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17806 eq34329
    | exact resolve eq34329 eq17806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17806 eq34329
  have eq34374 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq983 y
       have i₂ := eq34342
       grind)
    | exact superpose eq34342 eq983
    | (have j0 := eq983 y
       grind)
    | exact resolve eq983 eq34342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983 eq34342
  have eq34380 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq34374
  have eq34385 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34380
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34380
    | exact resolve eq34380 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34380
  have eq34393 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34002 eq34385
    | exact resolve eq34385 eq34002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34002 eq34385
  have eq34408 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34393 eq16477
    | exact resolve eq16477 eq34393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16477
  have eq34417 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq34408
  have eq34429 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq34417
    | exact resolve eq34417 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34417
  have eq34430 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) := by grind
  clear eq34429
  have eq34470 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq34430 eq27
    | exact resolve eq27 eq34430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34430
  have eq34511 : (M.op x y) = (σ y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq34470
       have r₂ := eq16775
       grind)
    | exact resolve eq34470 eq16775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16775 eq34470
  have eq34516 : y = (τ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34511 eq31
    | exact resolve eq31 eq34511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq34511
  have eq34797 : y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16803 eq34516
    | exact resolve eq34516 eq16803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16803 eq34516
  have eq34798 : y = (σ y) ∨ y = (M.op x y) := by grind
  clear eq34797
  have eq34840 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq34798
       grind)
    | exact superpose eq34798 eq18
    | exact resolve eq18 eq34798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34894 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq34798
  have eq35195 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34840 eq18158
    | exact resolve eq18158 eq34840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18158
  have eq35197 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34840 eq19528
    | exact resolve eq19528 eq34840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19528 eq34840
  have eq35211 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq35197
  have eq35213 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq35195
  have eq35237 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq35211
       have r₂ := eq34894
       grind)
    | exact resolve eq35211 eq34894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35211
  have eq35239 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq35213
       have r₂ := eq34894
       grind)
    | exact resolve eq35213 eq34894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35213
  have eq35553 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35237 eq566
    | exact resolve eq566 eq35237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35558 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35237 eq35553
    | exact resolve eq35553 eq35237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35237 eq35553
  have eq36054 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34393 eq35558
    | exact resolve eq35558 eq34393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34393 eq35558
  have eq36085 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq36054
  have eq36096 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq36085
       have r₂ := eq34894
       grind)
    | exact resolve eq36085 eq34894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34894 eq36085
  have eq36102 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq36096
    | exact resolve eq36096 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36096
  have eq36103 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq36102
  have eq36109 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36103 eq27
    | exact resolve eq27 eq36103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36103
  have eq36150 : y = (M.op x y) := by
    first
    | (have r₁ := eq36109
       have r₂ := eq35239
       grind)
    | exact resolve eq36109 eq35239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35239 eq36109
  have eq36158 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36150
       grind)
    | exact superpose eq36150 eq18
    | exact resolve eq18 eq36150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq36159 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq36150
       grind)
    | exact superpose eq36150 eq24
    | exact resolve eq24 eq36150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq36150
  have eq36214 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq36159 eq20
    | exact resolve eq20 eq36159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36159
  have eq36730 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq36158 eq574
    | exact resolve eq574 eq36158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq36158
  have eq36760 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq36730 eq15955
    | exact resolve eq15955 eq36730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955
  have eq36768 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq36730 eq177
    | exact resolve eq177 eq36730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36769 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq36730 eq566
    | exact resolve eq566 eq36730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq36730
  have eq36774 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq36769 eq36768
    | exact resolve eq36768 eq36769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36768
  have eq36779 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36760
    | exact resolve eq36760 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36760
  have eq36784 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq36214 eq36779
    | exact resolve eq36779 eq36214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36214 eq36779
  have eq36926 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq36784 eq177
    | exact resolve eq177 eq36784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq36933 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq36784 eq36926
    | exact resolve eq36926 eq36784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36784 eq36926
  have eq36945 : (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq36933 x x
       have i₂ := eq36774 x x
       grind)
    | exact superpose eq36774 eq36933
    | exact resolve eq36933 eq36774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36774 eq36933
  have eq36956 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq36945 eq26
    | exact resolve eq26 eq36945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq37077 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36945 eq24647
    | exact resolve eq24647 eq36945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24647 eq36945
  have eq37130 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq37077
  have eq37151 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq37130
    | exact resolve eq37130 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37130
  have eq37152 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq37151
  have eq37214 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36769 eq36956
    | exact resolve eq36956 eq36769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36769 eq36956
  have eq37472 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq37214 eq27
    | exact resolve eq27 eq37214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37214
  have eq37504 : False := by grind
  exact eq37504
