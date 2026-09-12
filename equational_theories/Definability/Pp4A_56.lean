import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4412`: `x ◇ (x ◇ y) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pxx_pyx_Equation4412 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4412 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4412.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq29 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq29
    | (have j0 := eq29 (M.op x y)
       grind)
    | exact resolve eq29 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq36 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq50 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq54 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 x X0 X3
       have i₂ := eq9 x X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq9 X2 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq31 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31
    | (have j0 := eq31 x
       grind)
    | exact resolve eq31 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op x X1) (M.op X0 (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op x X1)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op (M.op x y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x X1) x) := by
    intro X1
    first
    | (have i₁ := eq9 x x X1
       have i₂ := eq55 x
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op x y) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X1 x)
       have i₂ := eq55 X1
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X1) (σ x)) := by
    intro X1
    first
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) x) (σ x)) := by
    first
    | (have i₁ := eq91 (M.op sF2 x)
       have i₂ := eq55 sF2
       grind)
    | exact superpose eq55 eq91
    | exact resolve eq91 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq116 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) (τ X2))) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X2 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq10
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq121
    | exact resolve eq121 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq187 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq259 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1 (M.op X0 x)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq58 X2 (M.op X3 X1) X3
       have i₂ := eq58 X3 X1 X0
       grind)
    | (have i₁ := eq58 X2 (M.op X3 X1) X3
       have i₂ := eq58 X0 X1 X3
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 x))) = (M.op X1 (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 (M.op X1 x) X1
       have i₂ := eq55 X1
       grind)
    | exact superpose eq55 eq58
    | exact resolve eq58 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (σ x)))) = (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq58 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 X0 y x
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 X0 (σ y) (σ x)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X2 (M.op X2 X1) X3
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq54 X2 (M.op X2 X1) X3
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq54
    | exact resolve eq54 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X3 X1)
       have i₂ := eq58 X3 X1 X0
       grind)
    | (have i₁ := eq9 X2 X3 (M.op X3 X1)
       have i₂ := eq58 X0 X1 X3
       grind)
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X0 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (M.op x X1)
       have i₂ := eq58 x X1 X0
       grind)
    | (have i₁ := eq84 (M.op x X1)
       have i₂ := eq58 X0 X1 x
       grind)
    | exact superpose eq58 eq84
    | exact resolve eq84 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op y X1) y) := by
    intro X1
    first
    | (have i₁ := eq9 x y X1
       have i₂ := eq332 x
       grind)
    | (have i₁ := eq9 x y x
       have i₂ := eq332 x
       grind)
    | exact superpose eq332 eq9
    | (have j0 := eq9 x y X1
       grind)
    | exact resolve eq9 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 (M.op X0 y) X1
       have i₂ := eq332 X0
       grind)
    | (have i₁ := eq58 x (M.op x y) x
       have i₂ := eq332 X0
       grind)
    | exact superpose eq332 eq58
    | exact resolve eq58 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (M.op X0 y) X1
       have i₂ := eq332 X0
       grind)
    | (have i₁ := eq54 x (M.op x y) x
       have i₂ := eq332 X0
       grind)
    | exact superpose eq332 eq54
    | exact resolve eq54 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X1 y)
       have i₂ := eq332 X1
       grind)
    | (have i₁ := eq9 X0 x (M.op x y)
       have i₂ := eq332 X0
       grind)
    | exact superpose eq332 eq9
    | exact resolve eq9 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq372 x
       have i₂ := eq376 y x
       grind)
    | exact superpose eq376 eq372
    | exact resolve eq372 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq401 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) (σ y)) := by
    intro X1
    first
    | exact superpose eq334 eq9
    | (have j0 := eq9 (σ x) (σ y) X1
       grind)
    | exact resolve eq9 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | (have i₁ := eq401 x
       have i₂ := eq259 sF3 x
       grind)
    | exact superpose eq259 eq401
    | exact resolve eq401 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq427 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq412 eq334
    | exact resolve eq334 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op X1 X0)) = (M.op X1 (M.op (M.op (M.op x y) x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X1 (M.op X1 X0)
       have i₂ := eq85 X1 X0
       grind)
    | exact superpose eq85 eq85
    | exact resolve eq85 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op x y) x) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85 X2 (M.op X2 X1)
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq85 X2 (M.op X2 X1)
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq85
    | exact resolve eq85 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = (M.op (M.op (M.op x y) x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq85 X0 (M.op X0 x)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq85
    | exact resolve eq85 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op x y) x) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq59 eq85
    | exact resolve eq85 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) x) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq334 eq85
    | exact resolve eq85 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) x) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq85 x x
       grind)
    | exact superpose eq85 eq55
    | exact resolve eq55 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq332 x
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq332
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq332 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op x y) x) X0)) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X1 (M.op X2 X0) X2
       have i₂ := eq85 X2 X0
       grind)
    | exact superpose eq85 eq58
    | exact resolve eq58 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 (M.op (M.op x y) x))) (M.op (M.op x y) x)) = (k (M.op X0 (M.op X0 (M.op (M.op x y) x))) (M.op (M.op x y) x)) := by
    intro X0
    grind
  have eq501 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (M.op X0 (M.op (M.op (M.op x y) x) x))) := by
    intro X0
    first
    | exact superpose eq85 eq55
    | exact resolve eq55 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 (M.op (M.op (M.op x y) x) y))) := by
    intro X0
    first
    | exact superpose eq85 eq332
    | exact resolve eq332 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq85 eq332
    | exact resolve eq332 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq477 eq502
    | exact resolve eq502 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq512 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (M.op X0 (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq476 eq501
    | exact resolve eq501 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq501
  have eq526 : ∀ X0 : G, (k (M.op X0 (M.op X0 (M.op (M.op x y) x))) (M.op (M.op x y) x)) = (M.op (M.op (M.op x y) x) (M.op (M.op X0 (M.op X0 (M.op (M.op x y) x))) x)) := by
    intro X0
    first
    | exact superpose eq438 eq491
    | exact resolve eq491 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq528 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (M.op x y) x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq434 eq427
    | exact resolve eq427 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq533 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (k (M.op X0 (M.op X0 (M.op (M.op x y) x))) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq526 X0
       have i₂ := eq354 X0 (M.op sF0 x)
       grind)
    | exact superpose eq354 eq526
    | exact resolve eq526 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq535 : (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq512 eq533
    | exact resolve eq533 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq533
  have eq536 : (M.op (M.op x y) (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq438 eq535
    | exact resolve eq535 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq535
  have eq537 : (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq536
       have i₂ := eq55 sF0
       grind)
    | exact superpose eq55 eq536
    | exact resolve eq536 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq554 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op X0 x)) y) := by
    intro X0
    first
    | exact superpose eq55 eq477
    | exact resolve eq477 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq477 eq85
    | exact resolve eq85 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq565 : (M.op x (M.op x y)) = (M.op x (M.op (M.op (M.op x y) x) (M.op x y))) := by
    first
    | exact superpose eq434 eq564
    | exact resolve eq564 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq570 : (M.op x (M.op x y)) = (M.op x (M.op (M.op x (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq565
       have i₂ := eq376 sF0 x
       grind)
    | exact superpose eq376 eq565
    | exact resolve eq565 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq617 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq85 x X0
       have i₂ := eq92 x X0
       grind)
    | exact superpose eq92 eq85
    | exact resolve eq85 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq92
  have eq741 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259 X2 (M.op X2 X1)
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq259 X2 (M.op X2 X1)
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq259
    | exact resolve eq259 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq259 X0 (M.op X0 y)
       have i₂ := eq332 X0
       grind)
    | (have i₁ := eq259 x (M.op x y)
       have i₂ := eq332 X0
       grind)
    | exact superpose eq332 eq259
    | exact resolve eq259 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq334 eq259
    | exact resolve eq259 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq334
  have eq825 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op X1 X0)) = (M.op X1 (M.op (M.op x (M.op x y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq743 eq434
    | exact resolve eq434 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq831 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op X2 (M.op (M.op x (M.op x y)) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq743 eq484
    | exact resolve eq484 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq832 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq743 eq617
    | exact resolve eq617 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq833 : ∀ X0 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq743 eq745
    | exact resolve eq745 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq838 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op x (M.op x y)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq743 eq436
    | exact resolve eq436 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq843 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq743 eq506
    | exact resolve eq506 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq848 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op x (M.op x y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq743 eq440
    | exact resolve eq440 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq849 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op x (M.op x y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq743 eq441
    | exact resolve eq441 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq853 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x (M.op x y)) (σ x)) := by
    first
    | exact superpose eq743 eq100
    | exact resolve eq100 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq854 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq743 eq412
    | exact resolve eq412 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq855 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op x (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq743 eq528
    | exact resolve eq528 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq858 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op x (M.op x y)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq743 eq741
    | exact resolve eq741 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq878 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x (M.op x y)) X0)) = (M.op (M.op x (M.op x y)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq743 eq825
    | exact resolve eq825 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq917 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq33
       have i₂ := eq14 sF1 sF1
       grind)
    | exact superpose eq14 eq33
    | (have j1 := eq14 (σ (k (M.op x y) (M.op x y))) (σ (M.op x y))
       grind)
    | exact resolve eq33 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ (k x x)) (σ x)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq929 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq62
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq935 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq928
  have eq936 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq923
  have eq940 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq929
    | exact resolve eq929 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq1159 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op X0 y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq332 eq853
    | exact resolve eq853 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq1193 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X0 y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq332 eq854
    | exact resolve eq854 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1260 : ∀ X0 X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op X2 (M.op X0 (M.op X0 X1))) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq354 X2 (M.op X2 X1)
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq354 X2 (M.op X2 X1)
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq354
    | exact resolve eq354 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1555 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 (M.op x (M.op x y)))) (M.op x (M.op x y))) = (k (M.op X0 (M.op X0 (M.op x (M.op x y)))) (M.op x (M.op x y))) := by
    intro X0
    grind
  have eq1588 : (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) = (k (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq511 eq1555
    | exact resolve eq1555 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq1616 : (M.op x (M.op (M.op x (M.op x y)) (M.op x y))) = (k (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq878 eq1588
    | exact resolve eq1588 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1619 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq570 eq1616
    | exact resolve eq1616 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1759 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 y)))) := by
    intro X0 X1
    first
    | exact superpose eq332 eq511
    | exact resolve eq511 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq2410 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq537 eq917
    | (have j0 := eq917 (M.op (M.op x y) x) (M.op (M.op x y) x)
       grind)
    | exact resolve eq917 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2446 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by grind
  clear eq2410
  have eq2672 : (M.op (M.op (M.op x (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (M.op x (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by grind
  have eq2752 : (M.op (M.op (σ x) (M.op (M.op x (M.op x y)) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (M.op x (M.op x y)) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq878 eq2672
    | exact resolve eq2672 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq2672
  have eq2792 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq855 eq2752
    | exact resolve eq2752 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq2752
  have eq2811 : (M.op (M.op x (M.op x y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq849 eq2792
    | exact resolve eq2792 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq2792
  have eq2825 : (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq833 eq2811
    | exact resolve eq2811 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq2811
  have eq2829 : (M.op (M.op x (M.op x y)) (σ y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2825
       have i₂ := eq377 (M.op x sF0) sF3
       grind)
    | exact superpose eq377 eq2825
    | exact resolve eq2825 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2825
  have eq2831 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq854 eq2829
    | exact resolve eq2829 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq2829
  have eq3737 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq1619 eq917
    | (have j0 := eq917 (M.op x (M.op x y)) (M.op x (M.op x y))
       grind)
    | exact resolve eq917 eq1619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3741 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by grind
  clear eq3737
  have eq3798 : (M.op (M.op (M.op x y) x) (M.op x (M.op x x))) = (k (M.op (M.op x y) x) (M.op x (M.op x x))) := by grind
  clear eq80
  have eq3824 : (M.op (M.op x (M.op x y)) (M.op (M.op (M.op x y) x) x)) = (k (M.op (M.op x y) x) (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq3798
       have i₂ := eq838 x x (M.op sF0 x)
       grind)
    | exact superpose eq838 eq3798
    | exact resolve eq3798 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3798
  have eq3874 : (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) x)) = (k (M.op (M.op x y) x) (M.op x (M.op x x))) := by
    first
    | exact superpose eq743 eq3824
    | exact resolve eq3824 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq3824
  have eq3895 : (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq3874
       have i₂ := eq55 (M.op x sF0)
       grind)
    | exact superpose eq55 eq3874
    | exact resolve eq3874 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874
  have eq4131 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq2831 eq917
    | (have j0 := eq917 (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq917 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831
  have eq4135 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by grind
  clear eq4131
  have eq5257 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X1 (M.op X0 (M.op X0 (σ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq326 X0 X0
       have i₂ := eq58 X0 sF2 x
       grind)
    | (have i₁ := eq326 x x
       have i₂ := eq58 X0 sF2 x
       grind)
    | exact superpose eq58 eq326
    | exact resolve eq326 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5646 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X4 (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq352 X4 (M.op X4 X1) X2 X3
       have i₂ := eq58 X4 X1 X0
       grind)
    | (have i₁ := eq352 X4 (M.op X4 X1) X2 X3
       have i₂ := eq58 X0 X1 X4
       grind)
    | exact superpose eq58 eq352
    | exact resolve eq352 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5775 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op X0 X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq554 y
       have i₂ := eq352 X0 X1 y (M.op y x)
       grind)
    | (have i₁ := eq554 X0
       have i₂ := eq352 X0 x y x
       grind)
    | exact superpose eq352 eq554
    | exact resolve eq554 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq5779 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op X0 X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1159 sF2
       have i₂ := eq352 X0 X1 sF2 (M.op sF2 y)
       grind)
    | (have i₁ := eq1159 X0
       have i₂ := eq352 X0 y sF2 x
       grind)
    | exact superpose eq352 eq1159
    | (have j1 := eq352 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq1159 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq5781 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X0 X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1193 sF3
       have i₂ := eq352 X0 X1 sF3 (M.op sF3 y)
       grind)
    | (have i₁ := eq1193 X0
       have i₂ := eq352 X0 y sF3 x
       grind)
    | exact superpose eq352 eq1193
    | exact resolve eq1193 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq5885 : ∀ X0 X1 X2 : G, (M.op x (M.op x y)) = (M.op (M.op X1 (M.op X1 X2)) (M.op (M.op y X0) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq332 (M.op X1 (M.op X1 X2))
       have i₂ := eq352 X1 X2 y X0
       grind)
    | (have i₁ := eq332 (M.op y x)
       have i₂ := eq352 X0 X1 y x
       grind)
    | exact superpose eq352 eq332
    | exact resolve eq332 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5906 : ∀ X1 X2 : G, (M.op x (M.op x y)) = (M.op (M.op X1 (M.op X1 X2)) (M.op (M.op x (M.op x y)) y)) := by
    intro X1 X2
    first
    | (have i₁ := eq5885 x X1 X2
       have i₂ := eq376 y x
       grind)
    | exact superpose eq376 eq5885
    | exact resolve eq5885 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5885
  have eq6081 : ∀ X1 X2 : G, (M.op x (M.op x y)) = (M.op (M.op X1 (M.op X1 X2)) (M.op x (M.op x y))) := by
    intro X1 X2
    first
    | exact superpose eq386 eq5906
    | exact resolve eq5906 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5906
  have eq6211 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op X3 (M.op X3 X4)) (M.op X2 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq353 X3 X4 X2 (M.op X2 X1)
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq353 X3 X4 X2 (M.op X2 X1)
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq353
    | exact resolve eq353 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6297 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X1 (M.op X0 (M.op X0 (M.op X1 x)))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq325 eq353
    | exact resolve eq353 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq6416 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 (σ x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq326 X2 X1
       have i₂ := eq353 X0 X1 X2 (M.op X1 sF2)
       grind)
    | exact superpose eq353 eq326
    | exact resolve eq326 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq6449 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op x y)) X3) = (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq376 X3 (M.op X3 X2)
       have i₂ := eq353 X0 X1 X3 X2
       grind)
    | exact superpose eq353 eq376
    | exact resolve eq376 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6542 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X1 (M.op X1 X2)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (M.op X0 (M.op X0 X1))
       have i₂ := eq353 X0 X1 X2 sF2
       grind)
    | exact superpose eq353 eq59
    | exact resolve eq59 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7334 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X2 (M.op X0 (M.op X0 X1))) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5781 X2 (M.op X2 X1)
       have i₂ := eq58 X2 X1 X0
       grind)
    | (have i₁ := eq5781 X2 (M.op X2 X1)
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq5781
    | exact resolve eq5781 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8339 : ∀ X0 X1 : G, (M.op X1 (M.op x (M.op x y))) = (M.op X1 (M.op X0 (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X1 X1
       have i₂ := eq58 X1 y X0
       grind)
    | (have i₁ := eq374 X1 X1
       have i₂ := eq58 X0 y X1
       grind)
    | exact superpose eq58 eq374
    | exact resolve eq374 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq13124 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq935
       grind)
    | exact superpose eq935 eq10
    | exact resolve eq10 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq13158 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq3895
       have i₂ := eq58 x x X0
       grind)
    | (have i₁ := eq3895
       have i₂ := eq58 X0 x x
       grind)
    | exact superpose eq58 eq3895
    | exact resolve eq3895 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3895
  have eq14016 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op X0 (σ x))) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X0 (M.op X0 (σ x)))) = (k (M.op (M.op X0 (M.op X0 (σ x))) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    grind
  have eq14090 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X0 (M.op X0 (σ x)))) = (k (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq6416 eq14016
    | exact resolve eq14016 eq6416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6416 eq14016
  have eq14224 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (M.op X0 (σ x)))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq59 eq14090
    | exact resolve eq14090 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14090
  have eq14301 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq14224 X0
       have i₂ := eq838 X0 sF2 (M.op sF4 sF2)
       grind)
    | exact superpose eq838 eq14224
    | exact resolve eq14224 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq14224
  have eq14335 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) (σ x))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq832 eq14301
    | exact resolve eq14301 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq14301
  have eq14356 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq59 eq14335
    | exact resolve eq14335 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq14335
  have eq15377 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) x) = (M.op (M.op X2 (M.op X3 (M.op X0 (M.op X0 X1)))) x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1260 X3 (M.op X3 X1) X2
       have i₂ := eq58 X3 X1 X0
       grind)
    | (have i₁ := eq1260 X3 (M.op X3 X1) X2
       have i₂ := eq58 X0 X1 X3
       grind)
    | exact superpose eq58 eq1260
    | exact resolve eq1260 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq17756 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op X0 y)) (M.op x (M.op x y))) (M.op X0 (M.op X0 y))) = (k (M.op (M.op X0 (M.op X0 y)) (M.op x (M.op x y))) (M.op X0 (M.op X0 y))) := by
    intro X0
    grind
  have eq17837 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op X0 (M.op X0 y))) = (k (M.op x (M.op x y)) (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq6081 eq17756
    | exact resolve eq17756 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6081 eq17756
  have eq17976 : ∀ X0 : G, (M.op x (M.op x y)) = (k (M.op x (M.op x y)) (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq843 eq17837
    | exact resolve eq17837 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq17837
  have eq22438 : ∀ X0 X1 : G, (M.op X0 (M.op X0 x)) = (k (M.op X0 (M.op X0 x)) (M.op X1 (M.op X1 x))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq13158
    | exact resolve eq13158 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22609 : ∀ X0 : G, (τ (M.op (M.op (σ x) (σ y)) (σ x))) = (k (τ (M.op (M.op (σ x) (σ y)) (σ x))) (τ (M.op X0 (M.op X0 (σ x))))) := by
    intro X0
    first
    | exact superpose eq14356 eq160
    | exact resolve eq160 eq14356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14356
  have eq23541 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X2 (k X0 (τ X1))
       have i₂ := eq116 X0 X1 X2
       grind)
    | exact superpose eq116 eq49
    | exact resolve eq49 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23762 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (k (M.op X0 (M.op X0 y)) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | exact superpose eq332 eq17976
    | exact resolve eq17976 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25067 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X2 (M.op X3 (M.op X0 (M.op X0 X1)))) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7334 X3 (M.op X3 X1) X2
       have i₂ := eq58 X3 X1 X0
       grind)
    | (have i₁ := eq7334 X3 (M.op X3 X1) X2
       have i₂ := eq58 X0 X1 X3
       grind)
    | exact superpose eq58 eq7334
    | exact resolve eq7334 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7334
  have eq26014 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op x (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq376 X0 X0
       grind)
    | exact superpose eq376 eq187
    | exact resolve eq187 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq26018 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (k (τ (M.op X1 X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X1
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq187
    | exact resolve eq187 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26027 : ∀ X0 : G, (k (τ (M.op (M.op X0 (M.op X0 (σ x))) (M.op X0 (M.op X0 (σ x))))) (τ (M.op X0 (M.op X0 (σ x))))) = (τ (M.op (M.op (M.op X0 (M.op X0 (σ x))) (M.op X0 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (σ x)))) := by
    intro X0
    first
    | exact superpose eq5257 eq187
    | exact resolve eq187 eq5257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq5257
  have eq26073 : ∀ X0 : G, (k (τ (M.op (M.op X0 (M.op X0 (σ x))) (M.op X0 (M.op X0 (σ x))))) (τ (M.op X0 (M.op X0 (σ x))))) = (τ (M.op (M.op x (M.op x y)) (M.op (M.op (M.op X0 (M.op X0 (σ x))) (M.op X0 (M.op X0 (σ x)))) (σ x)))) := by
    intro X0
    first
    | exact superpose eq848 eq26027
    | exact resolve eq26027 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq26027
  have eq26143 : ∀ X0 : G, (k (τ (M.op (M.op X0 (M.op X0 (σ x))) (M.op X0 (M.op X0 (σ x))))) (τ (M.op X0 (M.op X0 (σ x))))) = (τ (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq26073 X0
       have i₂ := eq6449 X0 sF2 (M.op X0 (M.op X0 sF2)) sF2
       grind)
    | exact superpose eq6449 eq26073
    | exact resolve eq26073 eq6449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26073
  have eq26194 : ∀ X0 : G, (k (τ (M.op (M.op X0 (M.op X0 (σ x))) (M.op X0 (M.op X0 (σ x))))) (τ (M.op X0 (M.op X0 (σ x))))) = (k (τ (M.op (σ x) (σ x))) (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq26143 X0
       have i₂ := eq26018 (M.op x sF0) sF2
       grind)
    | exact superpose eq26018 eq26143
    | exact resolve eq26143 eq26018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26143
  have eq26239 : ∀ X0 : G, (k (τ (M.op (M.op X0 (M.op X0 (σ x))) (M.op X0 (M.op X0 (σ x))))) (τ (M.op X0 (M.op X0 (σ x))))) = (k (τ (M.op (σ x) (σ x))) x) := by
    intro X0
    first
    | exact superpose eq39 eq26194
    | exact resolve eq26194 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26194
  have eq26282 : ∀ X0 : G, (k (τ (M.op (M.op (σ x) (σ y)) (σ x))) (τ (M.op X0 (M.op X0 (σ x))))) = (k (τ (M.op (σ x) (σ x))) x) := by
    intro X0
    first
    | exact superpose eq6542 eq26239
    | exact resolve eq26239 eq6542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6542 eq26239
  have eq26316 : (τ (M.op (M.op (σ x) (σ y)) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq22609 eq26282
    | exact resolve eq26282 eq22609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22609 eq26282
  have eq33522 : ∀ X0 : G, (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) = (M.op X0 (M.op X0 (σ (M.op (M.op x y) x)))) := by
    intro X0
    first
    | exact superpose eq2446 eq58
    | exact resolve eq58 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33570 : ∀ X0 : G, (σ (M.op (M.op x y) x)) = (M.op X0 (M.op X0 (σ (M.op (M.op x y) x)))) := by
    intro X0
    first
    | exact superpose eq2446 eq33522
    | exact resolve eq33522 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446 eq33522
  have eq36057 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X4 X5)) X3) = (M.op (M.op X0 (M.op X1 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq352 X4 X5 X3 (M.op X3 (M.op X0 X2))
       have i₂ := eq323 X1 X2 X3 X0
       grind)
    | (have i₁ := eq352 X0 X1 X3 (M.op X0 (M.op X0 X1))
       have i₂ := eq323 X0 X1 X2 X3
       grind)
    | exact superpose eq323 eq352
    | exact resolve eq352 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq38559 : (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) = (M.op (M.op x (M.op x y)) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3741 eq377
    | exact resolve eq377 eq3741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq38587 : (σ (M.op x (M.op x y))) = (M.op (M.op x (M.op x y)) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3741 eq38559
    | exact resolve eq38559 eq3741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3741 eq38559
  have eq40572 : ∀ X0 : G, (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op X0 (M.op X0 (σ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq4135 eq58
    | exact resolve eq58 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40628 : ∀ X0 : G, (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (M.op X0 (σ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq4135 eq40572
    | exact resolve eq40572 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135 eq40572
  have eq45919 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X0 X0))) X0) X1) = (σ (k (τ (M.op (M.op x (M.op x y)) X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq116 (τ (M.op X0 X0)) X0 X1
       have i₂ := eq26014 X0
       grind)
    | exact superpose eq26014 eq116
    | exact resolve eq116 eq26014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26014
  have eq45960 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X0 X0))) X0) X1) = (k (M.op (M.op x (M.op x y)) X0) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45919 X0 X1
       have i₂ := eq50 (M.op (M.op x sF0) X0) (τ X1)
       grind)
    | exact superpose eq50 eq45919
    | exact resolve eq45919 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45919
  have eq46029 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X0 X0))) X0) X1) = (k (M.op (M.op x (M.op x y)) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45960 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq45960
    | exact resolve eq45960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45960
  have eq46087 : ∀ X0 X1 : G, (k (σ (k (τ (M.op X0 X0)) (τ X0))) X1) = (k (M.op (M.op x (M.op x y)) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46029 X0 X1
       have i₂ := eq23541 (τ (M.op X0 X0)) X0 X1
       grind)
    | exact superpose eq23541 eq46029
    | exact resolve eq46029 eq23541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46029
  have eq46122 : ∀ X0 X1 : G, (k (M.op (M.op x (M.op x y)) X0) X1) = (k (k (M.op X0 X0) (σ (τ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46087 X0 X1
       have i₂ := eq50 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq50 eq46087
    | exact resolve eq46087 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46087
  have eq46142 : ∀ X0 X1 : G, (k (M.op (M.op x (M.op x y)) X0) X1) = (k (k (M.op X0 X0) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46122 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46122
    | exact resolve eq46122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46122
  have eq46158 : ∀ X0 X1 : G, (k (M.op (M.op x (M.op x y)) X0) X1) = (k (M.op (M.op X0 X0) X0) X1) := by
    intro X0 X1
    grind
  clear eq46142
  have eq46955 : ∀ X0 X1 X2 : G, (k (k (σ (τ (M.op X1 X1))) X1) X2) = (σ (k (τ (M.op X0 (M.op X0 X1))) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 (τ (M.op X1 X1)) X1 X2
       have i₂ := eq26018 X0 X1
       grind)
    | exact superpose eq26018 eq116
    | exact resolve eq116 eq26018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq46966 : ∀ X0 X1 X2 : G, (k (k (σ (τ (M.op X1 X1))) X1) X2) = (k (M.op X0 (M.op X0 X1)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46955 X0 X1 X2
       have i₂ := eq50 (M.op X0 (M.op X0 X1)) (τ X2)
       grind)
    | exact superpose eq50 eq46955
    | exact resolve eq46955 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46955
  have eq47134 : ∀ X0 X1 X2 : G, (k (k (σ (τ (M.op X1 X1))) X1) X2) = (k (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46966 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq46966
    | exact resolve eq46966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46966
  have eq47227 : ∀ X0 X1 X2 : G, (k (σ (k (τ (M.op X1 X1)) (τ X1))) X2) = (k (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47134 X0 X1 X2
       have i₂ := eq23541 (τ (M.op X1 X1)) X1 X2
       grind)
    | exact superpose eq23541 eq47134
    | exact resolve eq47134 eq23541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23541 eq47134
  have eq47292 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 X1)) X2) = (k (k (M.op X1 X1) (σ (τ X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47227 X0 X1 X2
       have i₂ := eq50 (M.op X1 X1) (τ X1)
       grind)
    | exact superpose eq50 eq47227
    | exact resolve eq47227 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47227
  have eq47330 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 X1)) X2) = (k (k (M.op X1 X1) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47292 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq47292
    | exact resolve eq47292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47292
  have eq47344 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 X1)) X2) = (k (M.op (M.op X1 X1) X1) X2) := by
    intro X0 X1 X2
    grind
  clear eq47330
  have eq271263 : ∀ X0 X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ (M.op (σ x) (M.op (σ x) (σ y))))))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq40628 eq15377
    | exact resolve eq15377 eq40628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15377
  have eq330271 : ∀ X0 X1 X2 : G, (k (M.op (M.op x (M.op x y)) X0) X2) = (k (M.op (M.op X0 X1) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46158 X0 X2
       have i₂ := eq54 X0 X0 X1
       grind)
    | (have i₁ := eq46158 X0 X2
       have i₂ := eq54 X0 X1 X0
       grind)
    | exact superpose eq54 eq46158
    | exact resolve eq46158 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330280 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op (M.op x (M.op x y)) X3) X4) = (k (M.op (M.op X0 (M.op X1 (M.op X1 X2))) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq46158 X3 X4
       have i₂ := eq5646 X1 X2 X3 X3 X0
       grind)
    | (have i₁ := eq46158 (M.op X0 (M.op X0 X1)) X1
       have i₂ := eq5646 X0 X1 (M.op X0 (M.op X0 X1)) X3 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq5646 eq46158
    | exact resolve eq46158 eq5646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5646 eq46158
  have eq342456 : ∀ X0 X1 X3 : G, (k (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X3) = (k (M.op X0 (M.op (M.op x (M.op x y)) X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq47344 x (M.op X0 X1) X3
       have i₂ := eq831 X1 x X0
       grind)
    | exact superpose eq831 eq47344
    | exact resolve eq47344 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq342734 : ∀ X0 X1 : G, (k (M.op (M.op x y) x) X1) = (k (M.op X0 (M.op X0 x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47344 X0 x X1
       have i₂ := eq84 x
       grind)
    | exact superpose eq84 eq47344
    | exact resolve eq47344 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342746 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 (M.op X0 (M.op X0 y)))) X2) = (k (M.op (M.op (M.op X0 (M.op X0 y)) (M.op X0 (M.op X0 y))) (M.op x (M.op x y))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47344 X1 (M.op X0 (M.op X0 y)) X2
       have i₂ := eq8339 X0 (M.op (M.op X0 (M.op X0 y)) (M.op X0 (M.op X0 y)))
       grind)
    | (have i₁ := eq47344 X0 (M.op x (M.op x y)) X2
       have i₂ := eq8339 X0 (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))
       grind)
    | exact superpose eq8339 eq47344
    | exact resolve eq47344 eq8339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8339 eq47344
  have eq342954 : ∀ X0 X1 X2 : G, (k (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) X2) = (k (M.op X1 (M.op X1 (M.op X0 (M.op X0 y)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq342746 X1 X1 x
       have i₂ := eq330280 (M.op X1 (M.op X1 y)) X1 y (M.op x sF0) x
       grind)
    | exact superpose eq330280 eq342746
    | exact resolve eq342746 eq330280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330280 eq342746
  have eq343121 : ∀ X0 X1 X3 : G, (k (M.op (M.op x (M.op x y)) (M.op X0 X1)) X3) = (k (M.op X0 (M.op (M.op x (M.op x y)) X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq342456 X0 X1 X3
       have i₂ := eq330271 (M.op X0 X1) (M.op X0 X1) X3
       grind)
    | exact superpose eq330271 eq342456
    | exact resolve eq342456 eq330271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330271 eq342456
  have eq343311 : ∀ X0 X2 : G, (k (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) X2) = (k (M.op X0 (M.op X0 y)) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq342954 X0 x X2
       have i₂ := eq1759 X0 x
       grind)
    | exact superpose eq1759 eq342954
    | exact resolve eq342954 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759 eq342954
  have eq343446 : ∀ X0 X2 : G, (k (M.op x (M.op (M.op x (M.op x y)) (M.op x y))) X2) = (k (M.op X0 (M.op X0 y)) X2) := by
    intro X0 X2
    first
    | exact superpose eq343121 eq343311
    | exact resolve eq343311 eq343121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343121 eq343311
  have eq343502 : ∀ X0 X2 : G, (k (M.op x (M.op x y)) X2) = (k (M.op X0 (M.op X0 y)) X2) := by
    intro X0 X2
    first
    | exact superpose eq570 eq343446
    | exact resolve eq343446 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq343446
  have eq343764 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op X1 x))) X0) = (σ (k (M.op (M.op x y) x) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (M.op X1 (M.op X1 x))
       have i₂ := eq342734 X1 (τ X0)
       grind)
    | exact superpose eq342734 eq49
    | exact resolve eq49 eq342734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342734
  have eq343840 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op X1 x))) X0) = (k (σ (M.op (M.op x y) x)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq343764 X0 X1
       have i₂ := eq49 X0 (M.op sF0 x)
       grind)
    | exact superpose eq49 eq343764
    | exact resolve eq343764 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343764
  have eq344954 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op X1 y))) X0) = (σ (k (M.op x (M.op x y)) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (M.op X1 (M.op X1 y))
       have i₂ := eq343502 X1 (τ X0)
       grind)
    | (have i₁ := eq49 X0 (M.op x (M.op x y))
       have i₂ := eq343502 X0 (τ X0)
       grind)
    | exact superpose eq343502 eq49
    | exact resolve eq49 eq343502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343502
  have eq345030 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op X1 y))) X0) = (k (σ (M.op x (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq344954 X0 X1
       have i₂ := eq49 X0 (M.op x sF0)
       grind)
    | exact superpose eq49 eq344954
    | exact resolve eq344954 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344954
  have eq355812 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ (M.op (σ x) (M.op (σ x) (σ y))))))) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq40628 eq25067
    | exact resolve eq25067 eq40628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25067 eq40628
  have eq387871 : ∀ X0 X1 : G, (σ (k (M.op (M.op x y) x) X1)) = (k (σ (M.op X0 (M.op X0 x))) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq343840 eq15
    | exact resolve eq15 eq343840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343840
  have eq387953 : ∀ X0 X1 : G, (σ (k (M.op (M.op x y) x) X1)) = (σ (k (M.op X0 (M.op X0 x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq387871 X0 X1
       have i₂ := eq15 (M.op X0 (M.op X0 x)) X1
       grind)
    | exact superpose eq15 eq387871
    | exact resolve eq387871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387871
  have eq389611 : ∀ X0 X1 : G, (σ (k (M.op x (M.op x y)) X1)) = (k (σ (M.op X0 (M.op X0 y))) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq345030 eq15
    | exact resolve eq15 eq345030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345030
  have eq389694 : ∀ X0 X1 : G, (σ (k (M.op x (M.op x y)) X1)) = (σ (k (M.op X0 (M.op X0 y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq389611 X0 X1
       have i₂ := eq15 (M.op X0 (M.op X0 y)) X1
       grind)
    | exact superpose eq15 eq389611
    | exact resolve eq389611 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389611
  have eq392218 : ∀ X0 X1 : G, (σ (M.op (M.op x y) x)) = (σ (k (M.op X1 (M.op X1 x)) (M.op X0 (M.op X0 x)))) := by
    intro X0 X1
    first
    | exact superpose eq13158 eq387953
    | exact resolve eq387953 eq13158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13158 eq387953
  have eq392835 : ∀ X1 : G, (σ (M.op (M.op x y) x)) = (σ (M.op X1 (M.op X1 x))) := by
    intro X1
    first
    | (have i₁ := eq392218 x X1
       have i₂ := eq22438 X1 x
       grind)
    | exact superpose eq22438 eq392218
    | exact resolve eq392218 eq22438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22438 eq392218
  have eq399263 : ∀ X0 X1 : G, (σ (M.op x (M.op x y))) = (σ (k (M.op X1 (M.op X1 y)) (M.op X0 (M.op X0 y)))) := by
    intro X0 X1
    first
    | exact superpose eq17976 eq389694
    | exact resolve eq389694 eq17976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17976 eq389694
  have eq399865 : ∀ X1 : G, (σ (M.op x (M.op x y))) = (σ (M.op X1 (M.op X1 y))) := by
    intro X1
    first
    | (have i₁ := eq399263 x X1
       have i₂ := eq23762 X1 x
       grind)
    | exact superpose eq23762 eq399263
    | exact resolve eq399263 eq23762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23762 eq399263
  have eq444171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq940
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq940
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq940 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq444209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq444171
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq444171
    | exact resolve eq444171 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444171
  have eq444213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq444209
    | exact resolve eq444209 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444209
  have eq444214 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq444213
       have r₂ := eq28
       grind)
    | exact resolve eq444213 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444213
  have eq444216 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq444214 eq13124
    | exact resolve eq13124 eq444214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13124
  have eq444430 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq444214
  have eq444616 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq444216
       have r₂ := eq444430
       grind)
    | exact resolve eq444216 eq444430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444216 eq444430
  have eq444687 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40 eq444616
    | exact resolve eq444616 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444616
  have eq446828 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq444687
       grind)
    | exact superpose eq444687 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq444687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444687
  have eq446843 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq446828
  have eq447035 : (k (τ (σ x)) (τ (σ x))) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq446843 eq26018
    | exact resolve eq26018 eq446843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447081 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39 eq447035
    | exact resolve eq447035 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447035
  have eq447611 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq446843 eq447081
    | exact resolve eq447081 eq446843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446843 eq447081
  have eq447653 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq447611
  have eq447659 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39 eq447653
    | exact resolve eq447653 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447653
  have eq447670 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq447659
       grind)
    | exact superpose eq447659 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq447659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447659
  have eq447685 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq447670
  have eq447747 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x
       have i₂ := eq447685
       grind)
    | exact superpose eq447685 eq58
    | exact resolve eq58 eq447685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448042 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq447747 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq447747
    | (have j0 := eq447747 X0
       grind)
    | exact resolve eq447747 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447747
  have eq451481 : (σ (M.op x y)) = (σ (M.op (M.op x y) x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq392835 x
       have i₂ := eq448042 x
       grind)
    | exact superpose eq448042 eq392835
    | exact resolve eq392835 eq448042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451901 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op x x) ∨ (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq84 x
       have i₂ := eq448042 X0
       grind)
    | exact superpose eq448042 eq84
    | (have j1 := eq448042 X0
       grind)
    | exact resolve eq84 eq448042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452324 : (σ (M.op x y)) = (σ (M.op (M.op x y) x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq451481
    | exact resolve eq451481 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451481
  have eq524832 : (M.op (M.op x y) x) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq451901 x
       grind)
    | exact superpose eq451901 eq55
    | exact resolve eq55 eq451901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451901
  have eq525829 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq524832 eq55
    | exact resolve eq55 eq524832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526134 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq524832
  have eq611168 : ∀ X0 X1 : G, x = (M.op X0 (M.op X0 x)) ∨ (M.op x y) = (M.op X1 (M.op X1 x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq448042 X1
       have i₂ := eq525829 X0
       grind)
    | exact superpose eq525829 eq448042
    | (have j0 := eq448042 X1
       grind)
    | exact resolve eq448042 eq525829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448042
  have eq611171 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op X0 x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq526134
       have i₂ := eq525829 X0
       grind)
    | exact superpose eq525829 eq526134
    | exact resolve eq526134 eq525829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525829 eq526134
  have eq611342 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op X0 x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq611171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611171
  have eq611367 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq611168 X0 x
       grind)
    | (have r₁ := eq611168 X0 X0
       have r₂ := eq611342 X0
       grind)
    | exact resolve eq611168 eq611342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611168
  have eq612352 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq81 x
       have i₂ := eq611367 x
       grind)
    | exact superpose eq611367 eq81
    | exact resolve eq81 eq611367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq612379 : (σ x) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq392835 x
       have i₂ := eq611367 x
       grind)
    | exact superpose eq611367 eq392835
    | exact resolve eq392835 eq611367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392835
  have eq612411 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq611342 x
       have i₂ := eq611367 x
       grind)
    | exact superpose eq611367 eq611342
    | exact resolve eq611342 eq611367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612449 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq5775 x x
       have i₂ := eq611367 x
       grind)
    | exact superpose eq611367 eq5775
    | exact resolve eq5775 eq611367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612867 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq611367 eq537
    | (have j1 := eq611367 X0
       grind)
    | exact resolve eq537 eq611367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq613131 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq612411
  have eq613310 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq612449
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq612449
    | exact resolve eq612449 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612449
  have eq613320 : (σ x) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq612379
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq612379
    | exact resolve eq612379 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612379
  have eq613931 : x ≠ (M.op x y) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq612352
  have eq614031 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq613310 eq55
    | exact resolve eq55 eq613310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614052 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq613310 eq33570
    | exact resolve eq33570 eq613310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614115 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq613310 eq55
    | exact resolve eq55 eq613310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613310
  have eq614433 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq614052
    | (have j0 := eq614052 X0
       grind)
    | exact resolve eq614052 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614052
  have eq615673 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ x))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq613320 eq33570
    | exact resolve eq33570 eq613320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33570 eq613320
  have eq630752 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq614031 eq386
    | (have j1 := eq614031 X0
       grind)
    | exact resolve eq386 eq614031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq630776 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq614031 eq1619
    | (have j1 := eq614031 X0
       grind)
    | exact resolve eq1619 eq614031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614031
  have eq634860 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq614433 eq1619
    | (have j1 := eq614433 X0
       grind)
    | exact resolve eq1619 eq614433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq634890 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq614433 eq38587
    | (have j1 := eq614433 X0
       grind)
    | exact resolve eq38587 eq614433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38587 eq614433
  have eq635172 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21 eq634890
    | (have j0 := eq634890 X0
       grind)
    | exact resolve eq634890 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634890
  have eq636117 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq615673 eq5781
    | exact resolve eq5781 eq615673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615673
  have eq636990 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq27 eq636117
    | exact resolve eq636117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636117
  have eq649567 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq611342 x
       have i₂ := eq630752 x
       grind)
    | exact superpose eq630752 eq611342
    | (have r₁ := eq611342 x
       have r₂ := eq630752 x
       grind)
    | exact resolve eq611342 eq630752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630752
  have eq649918 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq649567
  have eq650437 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq649918 eq332
    | exact resolve eq332 eq649918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649918
  have eq650896 : x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq612867 x
       have i₂ := eq630776 x
       grind)
    | exact superpose eq630776 eq612867
    | exact resolve eq612867 eq630776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612867 eq630776
  have eq651190 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq650896
  have eq651396 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq651190 eq936
    | exact resolve eq936 eq651190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651407 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq651190 eq14
    | (have j0 := eq14 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq14 eq651190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651190
  have eq651410 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq651407
  have eq651415 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq651396
    | exact resolve eq651396 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651396
  have eq651416 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq651415
  have eq651506 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  have eq651520 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq651410 eq58
    | exact resolve eq58 eq651410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651808 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq651416 eq58
    | exact resolve eq58 eq651416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658318 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) x) = (M.op (σ (M.op x y)) x) := by
    first
    | exact superpose eq634860 eq354
    | exact resolve eq354 eq634860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634860
  have eq658890 : ∀ X1 X2 : G, (σ (M.op x y)) = (M.op (M.op X1 (M.op X2 (M.op X2 (M.op X1 x)))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) := by
    intro X1 X2
    first
    | exact superpose eq635172 eq6297
    | exact resolve eq6297 eq635172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6297 eq635172
  have eq673874 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op x y) x) = (M.op (σ (M.op x y)) x) := by
    first
    | exact superpose eq658318 eq936
    | exact resolve eq936 eq658318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658318
  have eq673892 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op x y) x) = (M.op (σ (M.op x y)) x) := by
    first
    | exact superpose eq21 eq673874
    | exact resolve eq673874 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673874
  have eq673893 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op x y) x) = (M.op (σ (M.op x y)) x) := by grind
  clear eq673892
  have eq686037 : (M.op (M.op x y) x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) x) ∨ (M.op (M.op x y) x) = (M.op (σ (M.op x y)) x) := by
    first
    | exact superpose eq673893 eq354
    | exact resolve eq354 eq673893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq673893
  have eq689100 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq651520 eq651410
    | exact resolve eq651410 eq651520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651410 eq651520
  have eq689152 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq689100 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689100
  have eq689672 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq689152 eq5781
    | exact resolve eq5781 eq689152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689817 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq689152 eq9
    | exact resolve eq9 eq689152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689821 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq689152 eq54
    | exact resolve eq54 eq689152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq689152
  have eq691037 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq689672 eq636990
    | exact resolve eq636990 eq689672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636990 eq689672
  have eq691234 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq691037
       have r₂ := eq613131
       grind)
    | exact resolve eq691037 eq613131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691037
  have eq692686 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq651808 eq651416
    | exact resolve eq651416 eq651808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651416
  have eq693061 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq692686 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692686
  have eq693550 : (τ (σ (M.op x y))) = (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq693061 eq26018
    | exact resolve eq26018 eq693061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693872 : (M.op (M.op x y) x) = (M.op (σ (M.op x y)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq693061 eq84
    | exact resolve eq84 eq693061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq693982 : (M.op x y) = (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq693550
    | exact resolve eq693550 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq693550
  have eq695318 : (M.op x y) ≠ (M.op (σ (M.op x y)) (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq693872 eq611342
    | exact resolve eq611342 eq693872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611342 eq693872
  have eq695551 : (M.op x y) ≠ (M.op (σ (M.op x y)) (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq695318
       have r₂ := eq613131
       grind)
    | exact resolve eq695318 eq613131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695318
  have eq718971 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq651808 x
       have i₂ := eq689817 x sF1
       grind)
    | exact superpose eq689817 eq651808
    | exact resolve eq651808 eq689817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651808
  have eq718974 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq693061 x
       have i₂ := eq689817 x sF1
       grind)
    | exact superpose eq689817 eq693061
    | exact resolve eq693061 eq689817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689817 eq693061
  have eq720055 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq718974
  have eq720056 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq718971
  have eq721036 : (M.op x y) = (k (τ (M.op (M.op x y) (σ (M.op x y)))) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq720056 eq693982
    | exact resolve eq693982 eq720056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693982 eq720056
  have eq721208 : (M.op x y) = (k (τ (M.op (M.op x y) (σ (M.op x y)))) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq721036
  have eq721801 : (σ (M.op x y)) = (k (M.op (M.op x y) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq721208 eq50
    | exact resolve eq50 eq721208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq721208
  have eq721807 : (σ (M.op x y)) = (k (M.op (M.op x y) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq721801
    | exact resolve eq721801 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721801
  have eq721836 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq720055 eq721807
    | exact resolve eq721807 eq720055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720055 eq721807
  have eq721843 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq721836
  have eq721848 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33 eq721843
    | exact resolve eq721843 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq721843
  have eq721891 : (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq651506 eq721848
    | exact resolve eq721848 eq651506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651506 eq721848
  have eq721939 : (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq721891
  have eq721970 : (σ (M.op x y)) = (σ (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq650437 eq721939
    | exact resolve eq721939 eq650437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650437 eq721939
  have eq722015 : (σ (M.op x y)) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq721970
       have r₂ := eq613131
       grind)
    | exact resolve eq721970 eq613131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721970
  have eq723144 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq689821 X0 (M.op X0 x)
       have i₂ := eq611367 X0
       grind)
    | exact superpose eq611367 eq689821
    | exact resolve eq689821 eq611367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611367 eq689821
  have eq724536 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq723144 X0
       grind)
    | (have r₁ := eq723144 X0
       have r₂ := eq613131
       grind)
    | exact resolve eq723144 eq613131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723144
  have eq748522 : ∀ X0 : G, (M.op x y) ≠ (M.op (σ (M.op x y)) (M.op X0 (M.op X0 x))) ∨ (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq55 eq695551
    | exact resolve eq695551 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695551
  have eq769316 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq724536 eq55
    | (have j1 := eq724536 X0
       grind)
    | exact resolve eq55 eq724536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830143 : (M.op x y) ≠ (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq769316
  have eq830147 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq830143
       have r₂ := eq614115
       grind)
    | exact resolve eq830143 eq614115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614115 eq830143
  have eq833990 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = X0 ∨ (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq830147 eq13
    | (have j0 := eq13 (k X0 (M.op x y)) X0
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq830147
       grind)
    | exact resolve eq13 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833991 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by grind
  have eq834019 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq830147 eq352
    | exact resolve eq352 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq834021 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq830147 eq353
    | exact resolve eq353 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq834037 : ∀ X0 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq830147 eq858
    | exact resolve eq858 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq834059 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq830147 eq5775
    | exact resolve eq5775 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5775
  have eq834060 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (σ x)) := by
    first
    | exact superpose eq830147 eq5779
    | exact resolve eq5779 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5779
  have eq834061 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) (σ y)) := by
    first
    | exact superpose eq830147 eq5781
    | exact resolve eq5781 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5781
  have eq834078 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq830147 eq6211
    | exact resolve eq6211 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6211
  have eq834094 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op (M.op (M.op x y) (M.op x y)) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq830147 eq6449
    | exact resolve eq6449 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6449
  have eq834122 : (k (τ (M.op x y)) (τ (M.op x y))) = (τ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq830147 eq26018
    | exact resolve eq26018 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26018
  have eq834132 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X3))) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq830147 eq36057
    | exact resolve eq36057 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36057
  have eq834189 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have j0 := eq833990 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833990
  have eq834356 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 (M.op X2 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq830147 eq834132
    | exact resolve eq834132 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834132
  have eq834366 : (τ (M.op x y)) = (k (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | exact superpose eq830147 eq834122
    | exact resolve eq834122 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834122
  have eq834394 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op (M.op x y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq830147 eq834094
    | exact resolve eq834094 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834094
  have eq834409 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op (M.op x y) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq830147 eq834078
    | exact resolve eq834078 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834078
  have eq834424 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq830147 eq834061
    | exact resolve eq834061 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834061
  have eq834425 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq830147 eq834060
    | exact resolve eq834060 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834060
  have eq834426 : (M.op x (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq830147 eq834059
    | exact resolve eq834059 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834059
  have eq834445 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq830147 eq834037
    | exact resolve eq834037 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834037
  have eq834456 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq830147 eq834021
    | exact resolve eq834021 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834021
  have eq834458 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq830147 eq834019
    | exact resolve eq834019 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834019
  have eq834482 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq830147 eq833991
    | exact resolve eq833991 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833991
  have eq838301 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq658890 x x
       have i₂ := eq834356 sF1 x x (M.op x x)
       grind)
    | exact superpose eq834356 eq658890
    | exact resolve eq658890 eq834356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658890 eq834356
  have eq838354 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) := by grind
  clear eq838301
  have eq845893 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) (M.op (σ (M.op x y)) x)) ∨ (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq748522 x
       have i₂ := eq834409 sF1 x x
       grind)
    | exact superpose eq834409 eq748522
    | (have j0 := eq748522 X0
       grind)
    | exact resolve eq748522 eq834409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748522 eq834409
  have eq846646 : ∀ X0 X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ (M.op (M.op x y) (σ y)))))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq834424 eq271263
    | exact resolve eq271263 eq834424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271263
  have eq846913 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ (M.op (M.op x y) (σ y)))))) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq834424 eq355812
    | exact resolve eq355812 eq834424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355812 eq834424
  have eq849915 : (k (τ (M.op (σ x) (σ x))) x) = (τ (M.op (M.op x y) (σ x))) := by
    first
    | exact superpose eq834425 eq26316
    | exact resolve eq26316 eq834425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26316 eq834425
  have eq857558 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq834445 eq834394
    | exact resolve eq834394 eq834445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834394 eq834445
  have eq859628 : ∀ X1 : G, (k (M.op X1 X1) X1) = (M.op (M.op x y) X1) := by
    intro X1
    grind
  have eq861447 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq834482 eq936
    | exact resolve eq936 eq834482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq834482
  have eq872898 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq861447
    | exact resolve eq861447 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861447
  have eq872899 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq872898
  have eq877851 : (M.op (M.op x y) x) = (M.op (σ (M.op x y)) x) ∨ (M.op (M.op x y) x) = (M.op (σ (M.op x y)) x) := by
    first
    | exact superpose eq872899 eq686037
    | exact resolve eq686037 eq872899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686037
  have eq878478 : (M.op (M.op x y) x) = (M.op (σ (M.op x y)) x) := by grind
  clear eq877851
  have eq880769 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq878478 eq845893
    | (have j0 := eq845893 X0
       grind)
    | exact resolve eq845893 eq878478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845893 eq878478
  have eq881817 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) x) ∨ (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq880769 X0
       have i₂ := eq55 sF0
       grind)
    | exact superpose eq55 eq880769
    | (have j0 := eq880769 X0
       grind)
    | exact resolve eq880769 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq880769
  have eq883870 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq872899 eq58
    | exact resolve eq58 eq872899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883911 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq872899 eq883870
    | exact resolve eq883870 eq872899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872899 eq883870
  have eq885862 : (τ (τ (M.op x y))) = (k (τ (τ (M.op x y))) (τ (τ (M.op x y)))) := by
    first
    | exact superpose eq834366 eq160
    | exact resolve eq160 eq834366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq834366
  have eq889013 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq883911 eq834458
    | exact resolve eq834458 eq883911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883911
  have eq943728 : (σ (τ (τ (M.op x y)))) = (M.op (σ (τ (τ (M.op x y)))) (σ (τ (τ (M.op x y))))) ∨ (σ (τ (τ (M.op x y)))) = (M.op (σ (τ (τ (M.op x y)))) (σ (τ (τ (M.op x y))))) ∨ (σ (τ (τ (M.op x y)))) = (M.op (σ (τ (τ (M.op x y)))) (σ (τ (τ (M.op x y))))) := by
    first
    | exact superpose eq885862 eq917
    | (have j0 := eq917 (τ (τ (M.op x y))) (τ (τ (M.op x y)))
       grind)
    | exact resolve eq917 eq885862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq885862
  have eq943749 : (σ (τ (τ (M.op x y)))) = (M.op (σ (τ (τ (M.op x y)))) (σ (τ (τ (M.op x y))))) := by grind
  clear eq943728
  have eq943762 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | (have i₁ := eq943749
       have i₂ := eq11 (τ sF0)
       grind)
    | exact superpose eq11 eq943749
    | exact resolve eq943749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943749
  have eq944005 : ∀ X0 : G, (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = X0 ∨ (M.op X0 X0) = (k X0 (τ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq943762 eq13
    | (have j0 := eq13 (k X0 (τ (M.op x y))) X0
       grind)
    | (have r₁ := eq13 X0 (τ (M.op x y))
       have r₂ := eq943762
       grind)
    | exact resolve eq13 eq943762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944012 : ∀ X0 : G, (M.op (τ (M.op x y)) (τ (M.op x y))) = (M.op X0 (M.op X0 (τ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq943762 eq58
    | exact resolve eq58 eq943762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq944035 : (M.op (τ (M.op x y)) (τ (M.op x y))) = (M.op (M.op x y) (τ (M.op x y))) := by
    first
    | exact superpose eq943762 eq834458
    | exact resolve eq834458 eq943762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944042 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ (M.op x y))) ∨ (τ (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq944005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944005
  have eq944047 : (τ (M.op x y)) = (M.op (M.op x y) (τ (M.op x y))) := by
    first
    | exact superpose eq943762 eq944035
    | exact resolve eq944035 eq943762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944035
  have eq944069 : ∀ X0 : G, (τ (M.op x y)) = (M.op X0 (M.op X0 (τ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq943762 eq944012
    | exact resolve eq944012 eq943762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943762 eq944012
  have eq944144 : (τ (M.op x y)) = (M.op x (τ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq944047 eq724536
    | exact resolve eq724536 eq944047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724536
  have eq998446 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (M.op x y)) ∨ (τ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq944042 eq49
    | (have j1 := eq944042 X0
       grind)
    | exact resolve eq49 eq944042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq944042
  have eq1062196 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (M.op x y)) ∨ (σ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11 X0
       have i₂ := eq998446 (τ X0)
       grind)
    | exact superpose eq998446 eq11
    | (have j1 := eq998446 X0
       grind)
    | exact resolve eq11 eq998446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998446
  have eq1065424 : (σ (M.op x x)) = (k (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq1062196 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1062196
    | (have j0 := eq1062196 x
       grind)
    | exact resolve eq1062196 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065425 : (σ (M.op y y)) = (k (σ y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq1062196 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1062196
    | (have j0 := eq1062196 y
       grind)
    | exact resolve eq1062196 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062196
  have eq1065492 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1065424 eq834189
    | (have j0 := eq834189 (σ x)
       grind)
    | exact resolve eq834189 eq1065424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065424
  have eq1065497 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (M.op x y) = (σ x) := by grind
  clear eq1065492
  have eq1065518 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq1065425 eq834189
    | (have j0 := eq834189 (σ y)
       grind)
    | exact resolve eq834189 eq1065425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834189 eq1065425
  have eq1065523 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq1065518
  have eq1065536 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1065497
       have i₂ := eq447685
       grind)
    | exact superpose eq447685 eq1065497
    | exact resolve eq1065497 eq447685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447685
  have eq1065546 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1065497
       grind)
    | exact superpose eq1065497 eq10
    | exact resolve eq10 eq1065497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065551 : (k (M.op (σ x) (σ x)) (σ x)) = (σ (k (M.op x x) x)) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq31 (M.op x x)
       have i₂ := eq1065497
       grind)
    | exact superpose eq1065497 eq31
    | exact resolve eq31 eq1065497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1065556 : (σ (M.op (M.op x y) x)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq1065551
       have i₂ := eq859628 x
       grind)
    | exact superpose eq859628 eq1065551
    | exact resolve eq1065551 eq859628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065551
  have eq1065557 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1065536
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1065536
    | exact resolve eq1065536 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065536
  have eq1065559 : (σ (M.op (M.op x y) x)) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq1065556
       have i₂ := eq859628 sF2
       grind)
    | exact superpose eq859628 eq1065556
    | exact resolve eq1065556 eq859628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065556
  have eq1065688 : (k (M.op (σ y) (σ y)) (σ y)) = (σ (k (M.op y y) y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq1065523
       grind)
    | exact superpose eq1065523 eq36
    | exact resolve eq36 eq1065523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1065523
  have eq1065691 : (k (M.op (σ y) (σ y)) (σ y)) = (σ (M.op (M.op x y) y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq1065688
       have i₂ := eq859628 y
       grind)
    | exact superpose eq859628 eq1065688
    | exact resolve eq1065688 eq859628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065688
  have eq1065692 : (σ (M.op x (M.op x y))) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq834426 eq1065691
    | exact resolve eq1065691 eq834426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834426 eq1065691
  have eq1065693 : (σ (M.op x (M.op x y))) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq1065692
       have i₂ := eq859628 sF3
       grind)
    | exact superpose eq859628 eq1065692
    | exact resolve eq1065692 eq859628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065692
  have eq1065843 : (k (M.op x x) x) = (τ (M.op (M.op x y) (σ x))) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1065546 eq849915
    | exact resolve eq849915 eq1065546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849915 eq1065546
  have eq1065883 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) (σ x))) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq1065843
       have i₂ := eq859628 x
       grind)
    | exact superpose eq859628 eq1065843
    | exact resolve eq1065843 eq859628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859628 eq1065843
  have eq1065952 : (σ (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1065559 eq452324
    | exact resolve eq452324 eq1065559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452324 eq1065559
  have eq1066073 : ∀ X0 : G, (σ (M.op X0 (M.op X0 y))) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq1065693 eq399865
    | exact resolve eq399865 eq1065693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399865
  have eq1066076 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq1065693 eq722015
    | exact resolve eq722015 eq1065693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722015 eq1065693
  have eq1068496 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1065557 eq834456
    | exact resolve eq834456 eq1065557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834456 eq1065557
  have eq1068513 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq1068496
    | exact resolve eq1068496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068496
  have eq1071165 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq1066076 eq691234
    | exact resolve eq691234 eq1066076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066076
  have eq1071246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ y) := by grind
  clear eq1071165
  have eq1071277 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq1071246
       have r₂ := eq28
       grind)
    | exact resolve eq1071246 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071246
  have eq1076442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1068513 eq1065952
    | exact resolve eq1065952 eq1068513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065952 eq1068513
  have eq1076518 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (M.op x y) = (σ x) := by grind
  clear eq1076442
  have eq1076541 : x = (M.op x x) ∨ (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq1076518
       have r₂ := eq28
       grind)
    | exact resolve eq1076518 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076518
  have eq1076576 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq1065497
       have i₂ := eq1076541
       grind)
    | exact superpose eq1076541 eq1065497
    | exact resolve eq1065497 eq1076541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065497 eq1076541
  have eq1076683 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) := by grind
  clear eq1076576
  have eq1076689 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq1076683
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1076683
    | exact resolve eq1076683 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076683
  have eq1076945 : (M.op (σ x) (σ x)) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1076689 eq834458
    | exact resolve eq834458 eq1076689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834458
  have eq1078530 : (σ x) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1076945 eq1076689
    | exact resolve eq1076689 eq1076945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076689 eq1076945
  have eq1078602 : (σ x) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (σ x) := by grind
  clear eq1078530
  have eq1078724 : (τ (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1078602 eq1065883
    | exact resolve eq1065883 eq1078602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065883
  have eq1078750 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ x) := by
    intro X0
    first
    | exact superpose eq1078602 eq857558
    | exact resolve eq857558 eq1078602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078602
  have eq1078833 : (τ (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ x) := by grind
  clear eq1078724
  have eq1078858 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq39 eq1078833
    | exact resolve eq1078833 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078833
  have eq1079123 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1078858 eq1071277
    | exact resolve eq1071277 eq1078858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079153 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ x) := by
    intro X0
    first
    | exact superpose eq1078858 eq857558
    | exact resolve eq857558 eq1078858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857558 eq1078858
  have eq1079600 : y = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1079123 eq40
    | exact resolve eq40 eq1079123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1080725 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1078750 eq27
    | (have j1 := eq1078750 (σ y)
       grind)
    | exact resolve eq27 eq1078750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078750
  have eq1081890 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1079123 eq1080725
    | exact resolve eq1080725 eq1079123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080725
  have eq1082008 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1081890
  have eq1082025 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq830147 eq1082008
    | exact resolve eq1082008 eq830147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830147 eq1082008
  have eq1082699 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1082025 eq28
    | exact resolve eq28 eq1082025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082025
  have eq1084437 : (τ (M.op x y)) = (M.op x (τ (M.op x y))) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1079153 eq944047
    | exact resolve eq944047 eq1079153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079153
  have eq1090188 : y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq1079600 eq1084437
    | exact resolve eq1084437 eq1079600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079600 eq1084437
  have eq1090241 : y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1090188
  have eq1090254 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1090241
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1090241
    | exact resolve eq1090241 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090241
  have eq1090467 : x = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1090254 eq39
    | exact resolve eq39 eq1090254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090254
  have eq1093778 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1090467 eq944047
    | exact resolve eq944047 eq1090467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944047 eq1090467
  have eq1093865 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1093778
       have r₂ := eq613931
       grind)
    | exact resolve eq1093778 eq613931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613931 eq1093778
  have eq1094016 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1093865 eq1071277
    | exact resolve eq1071277 eq1093865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071277
  have eq1094886 : y = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1094016 eq40
    | exact resolve eq40 eq1094016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094016
  have eq1103418 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1094886 eq944144
    | exact resolve eq944144 eq1094886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944144 eq1094886
  have eq1103516 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1103418
       have r₂ := eq613131
       grind)
    | exact resolve eq1103418 eq613131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103418
  have eq1103518 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1103516
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1103516
    | exact resolve eq1103516 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1103516
  have eq1103519 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq1103518
  have eq1103646 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1103519 eq1093865
    | exact resolve eq1093865 eq1103519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093865 eq1103519
  have eq1103791 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1103646
  have eq1103874 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1103791 eq21
    | exact resolve eq21 eq1103791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103791
  have eq1104643 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1103874
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1103874
    | exact resolve eq1103874 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103874
  have eq1105067 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1104643 eq691234
    | exact resolve eq691234 eq1104643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691234
  have eq1105116 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1104643 eq1079123
    | exact resolve eq1079123 eq1104643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079123 eq1104643
  have eq1105137 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by grind
  clear eq1105116
  have eq1105149 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1105137
       have r₂ := eq1082699
       grind)
    | exact resolve eq1105137 eq1082699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082699 eq1105137
  have eq1105185 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq1105067
       have r₂ := eq613131
       grind)
    | exact resolve eq1105067 eq613131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613131 eq1105067
  have eq1105229 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq838354 eq1105185
    | exact resolve eq1105185 eq838354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838354 eq1105185
  have eq1105237 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq1105229
       have r₂ := eq28
       grind)
    | exact resolve eq1105229 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105229
  have eq1106876 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ (M.op (M.op x y) (σ y)))))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq1105237 eq846646
    | exact resolve eq846646 eq1105237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846646
  have eq1106949 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq1105237 eq881817
    | (have j0 := eq881817 X0
       grind)
    | (have r₁ := eq881817 X0
       have r₂ := eq1105237
       grind)
    | exact resolve eq881817 eq1105237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881817
  have eq1108436 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have j0 := eq1106949 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106949
  have eq1113955 : x = (τ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1105149 eq39
    | exact resolve eq39 eq1105149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1105149
  have eq1114661 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1113955 eq944069
    | exact resolve eq944069 eq1113955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113955
  have eq1114817 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1114661 x
       have i₂ := eq1108436 x
       grind)
    | exact superpose eq1108436 eq1114661
    | exact resolve eq1114661 eq1108436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108436 eq1114661
  have eq1114818 : x = (M.op x y) := by grind
  clear eq1114817
  have eq1114825 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1114818 eq21
    | exact resolve eq21 eq1114818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1114835 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1114818 eq332
    | exact resolve eq332 eq1114818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq1118255 : ∀ X0 X1 X2 : G, (M.op x (σ y)) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ (M.op x (σ y)))))) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1114818 eq846913
    | exact resolve eq846913 eq1114818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846913
  have eq1118825 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq1114818 eq889013
    | exact resolve eq889013 eq1114818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889013
  have eq1120480 : ∀ X0 : G, (τ x) = (M.op X0 (M.op X0 (τ x))) := by
    intro X0
    first
    | exact superpose eq1114818 eq944069
    | exact resolve eq944069 eq1114818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944069
  have eq1123809 : ∀ X0 : G, (M.op x (σ y)) = (σ (M.op X0 (M.op X0 y))) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq1114818 eq1066073
    | exact resolve eq1066073 eq1114818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066073
  have eq1127161 : x = (M.op x x) := by
    first
    | exact superpose eq1114818 eq1105237
    | exact resolve eq1105237 eq1114818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105237
  have eq1127277 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 (M.op X1 (M.op X2 (σ (M.op x (σ y)))))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq1114818 eq1106876
    | exact resolve eq1106876 eq1114818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106876
  have eq1130628 : ∀ X0 : G, x = (σ y) ∨ (M.op x (σ y)) = (σ (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq1114818 eq1123809
    | (have j0 := eq1123809 X0
       grind)
    | exact resolve eq1123809 eq1114818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114818 eq1123809
  have eq1134316 : ∀ X0 : G, x = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1114835 X0
       have i₂ := eq1127161
       grind)
    | exact superpose eq1127161 eq1114835
    | exact resolve eq1114835 eq1127161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114835 eq1127161
  have eq1134319 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1114825
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1114825
    | exact resolve eq1114825 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114825
  have eq1137023 : (σ x) = (M.op x (σ y)) ∨ x = (σ y) := by
    first
    | (have i₁ := eq1130628 x
       have i₂ := eq1134316 x
       grind)
    | exact superpose eq1134316 eq1130628
    | exact resolve eq1130628 eq1134316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130628
  have eq1137062 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1134319 eq23
    | exact resolve eq23 eq1134319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1137063 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1134319 eq27
    | exact resolve eq27 eq1134319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1134319
  have eq1143745 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1118825 eq1137063
    | exact resolve eq1137063 eq1118825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118825 eq1137063
  have eq1143763 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (σ y) := by
    first
    | (have i₁ := eq1137023
       have i₂ := eq1137062
       grind)
    | exact superpose eq1137062 eq1137023
    | exact resolve eq1137023 eq1137062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137023
  have eq1145859 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ (M.op (σ x) (σ y)))))) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1143745 eq1118255
    | exact resolve eq1118255 eq1143745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118255
  have eq1146056 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 (M.op X1 (M.op X2 (σ (M.op (σ x) (σ y)))))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq1143745 eq1127277
    | exact resolve eq1127277 eq1143745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127277
  have eq1146262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ y) := by
    first
    | exact superpose eq1143745 eq1143763
    | exact resolve eq1143763 eq1143745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143745 eq1143763
  have eq1147725 : x = (σ y) := by
    first
    | (have r₁ := eq1146262
       have r₂ := eq28
       grind)
    | exact resolve eq1146262 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146262
  have eq1148579 : x = (σ y) := by
    first
    | exact superpose eq1147725 eq25
    | exact resolve eq25 eq1147725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1148582 : y = (τ x) := by
    first
    | exact superpose eq1147725 eq40
    | exact resolve eq40 eq1147725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1150339 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ (M.op (σ x) (σ y)))))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq1147725 eq1145859
    | exact resolve eq1145859 eq1147725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145859 eq1147725
  have eq1151099 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1146056 eq1150339
    | exact resolve eq1150339 eq1146056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146056 eq1150339
  have eq1152156 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1120480 X0
       have i₂ := eq1148582
       grind)
    | exact superpose eq1148582 eq1120480
    | exact resolve eq1120480 eq1148582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120480 eq1148582
  have eq1153661 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1151099 eq28
    | exact resolve eq28 eq1151099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1151099
  have eq1154673 : x = y := by
    first
    | (have i₁ := eq1152156 x
       have i₂ := eq1134316 x
       grind)
    | exact superpose eq1134316 eq1152156
    | exact resolve eq1152156 eq1134316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134316 eq1152156
  have eq1156234 : x = (σ x) := by
    first
    | (have i₁ := eq1148579
       have i₂ := eq1154673
       grind)
    | exact superpose eq1154673 eq1148579
    | exact resolve eq1148579 eq1154673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148579 eq1154673
  have eq1159423 : x = (σ (M.op x y)) := by
    first
    | (have i₁ := eq1156234
       have i₂ := eq1137062
       grind)
    | exact superpose eq1137062 eq1156234
    | exact resolve eq1156234 eq1137062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137062 eq1156234
  have eq1160520 : False := by grind
  exact eq1160520

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyx_y_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
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
  have eq57 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
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
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq212 : (M.op x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ x)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 y)
       have i₂ := eq213 X0 y
       grind)
    | (have i₁ := eq56 (M.op x y)
       have i₂ := eq213 X0 y
       grind)
    | exact superpose eq213 eq56
    | exact resolve eq56 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 y)
       have i₂ := eq213 X0 sF3
       grind)
    | (have i₁ := eq57 (M.op x y)
       have i₂ := eq213 X0 sF3
       grind)
    | exact superpose eq213 eq57
    | exact resolve eq57 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq373 X0
       have i₂ := eq213 X0 (M.op sF0 sF3)
       grind)
    | (have i₁ := eq373 x
       have i₂ := eq213 X0 (M.op sF0 sF3)
       grind)
    | exact superpose eq213 eq373
    | exact resolve eq373 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq375 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq213 X0 (M.op sF0 y)
       grind)
    | (have i₁ := eq372 x
       have i₂ := eq213 X0 (M.op sF0 y)
       grind)
    | exact superpose eq213 eq372
    | exact resolve eq372 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq384 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq57 eq374
    | exact resolve eq374 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq385 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq375 X0
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq375
    | exact resolve eq375 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq395 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X0 y) X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op X2 (M.op X0 (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq222 eq56
    | exact resolve eq56 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq222 eq57
    | exact resolve eq57 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq222 eq491
    | exact resolve eq491 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq493 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq222 eq490
    | exact resolve eq490 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq502 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq57 eq492
    | exact resolve eq492 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq503 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq493 X0
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq493
    | exact resolve eq493 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq548 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq384 sF4
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq384
    | exact resolve eq384 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq697 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 y X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq51
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X2 X1 X0 X0
       have i₂ := eq55 X0 X1 X0
       grind)
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq792 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq222 eq698
    | (have j0 := eq698 X0 (σ x)
       grind)
    | exact resolve eq698 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq793 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq697 X0 x
       have i₂ := eq213 x X0
       grind)
    | (have i₁ := eq697 x x
       have i₂ := eq213 X0 x
       grind)
    | exact superpose eq213 eq697
    | (have j0 := eq697 X0 x
       grind)
    | exact resolve eq697 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq1156 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 X1)
       have i₂ := eq52 X1 y (M.op X0 X1) X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1157 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op x X0)
       have i₂ := eq52 X0 sF3 (M.op x X0) x
       grind)
    | exact superpose eq52 eq57
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1206 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq222 eq1157
    | exact resolve eq1157 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1207 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1156 X0 X1
       have i₂ := eq213 (M.op X0 X1) (M.op X1 (M.op X1 y))
       grind)
    | exact superpose eq213 eq1156
    | exact resolve eq1156 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1232 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq1206
    | exact resolve eq1206 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1233 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1207 X0 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq1207
    | exact resolve eq1207 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1422 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq2075 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq222 eq792
    | exact resolve eq792 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq2157 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2075 eq51
    | exact resolve eq51 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2183 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2157 X0
       have i₂ := eq14 sF4 sF3 sF4
       grind)
    | exact superpose eq14 eq2157
    | exact resolve eq2157 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157
  have eq2188 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | (have i₁ := eq2183 x
       have i₂ := eq14 sF4 sF3 x
       grind)
    | exact superpose eq14 eq2183
    | exact resolve eq2183 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183
  have eq2189 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq57 eq2188
    | exact resolve eq2188 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188
  have eq2200 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq793 y
       have i₂ := eq213 sF0 y
       grind)
    | exact superpose eq213 eq793
    | exact resolve eq793 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2201 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq222 eq793
    | exact resolve eq793 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq2253 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2200 eq51
    | exact resolve eq51 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq2279 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2253 X0
       have i₂ := eq14 sF0 y sF0
       grind)
    | exact superpose eq14 eq2253
    | exact resolve eq2253 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq2284 : (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2279 x
       have i₂ := eq14 sF0 y x
       grind)
    | exact superpose eq14 eq2279
    | exact resolve eq2279 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2279
  have eq2285 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2284
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq2284
    | exact resolve eq2284 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284
  have eq2400 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq57 eq1232
    | exact resolve eq1232 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1232
  have eq2496 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq502 eq2400
    | exact resolve eq2400 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400
  have eq2511 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2189 eq2496
    | exact resolve eq2496 eq2189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189 eq2496
  have eq2532 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2511 y
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq2511
    | exact resolve eq2511 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq2601 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq1233 X0 (M.op X0 y)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq1233
    | exact resolve eq1233 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2718 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq385 eq2601
    | exact resolve eq2601 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq2601
  have eq2737 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2285 eq2718
    | exact resolve eq2718 eq2285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285 eq2718
  have eq2801 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1233 eq2737
    | exact resolve eq2737 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2802 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq503 eq2737
    | exact resolve eq2737 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq2737
  have eq4082 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op y X1)) y) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq395 (M.op X2 X1) X3 y
       have i₂ := eq51 X2 X1 y X0
       grind)
    | exact superpose eq51 eq395
    | exact resolve eq395 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4272 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq4082 x X1 X2 X3
       have i₂ := eq213 (M.op x (M.op y X1)) X3
       grind)
    | exact superpose eq213 eq4082
    | exact resolve eq4082 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4082
  have eq4334 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq2801 eq4272
    | (have j0 := eq4272 y x X3
       grind)
    | exact resolve eq4272 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4272
  have eq4591 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op X2 (M.op (M.op x y) (σ y))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396 (M.op X0 y) X1 X2
       have i₂ := eq213 X0 sF3
       grind)
    | (have i₁ := eq396 (M.op x y) X1 X2
       have i₂ := eq213 X0 sF3
       grind)
    | exact superpose eq213 eq396
    | exact resolve eq396 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4632 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq2201 eq396
    | exact resolve eq396 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4790 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq222 eq4632
    | exact resolve eq4632 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq4632
  have eq4817 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq396 eq4591
    | exact resolve eq4591 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq4591
  have eq4856 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq648 eq4790
    | exact resolve eq4790 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4790
  have eq4878 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq648 eq4817
    | exact resolve eq4817 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq4817
  have eq4905 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2802 eq4856
    | exact resolve eq4856 eq2802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4856
  have eq4926 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq2802 eq4878
    | exact resolve eq4878 eq2802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802 eq4878
  have eq4944 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq4334 eq4905
    | exact resolve eq4905 eq4334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4905
  have eq4964 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq4334 eq4926
    | exact resolve eq4926 eq4334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334 eq4926
  have eq4988 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4964 X0 X1
       have i₂ := eq395 X0 X1 sF4
       grind)
    | exact superpose eq395 eq4964
    | exact resolve eq4964 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq4964
  have eq5816 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4988 X1 X2
       have i₂ := eq53 sF0 X1 X2 x
       grind)
    | (have i₁ := eq4988 X1 X2
       have i₂ := eq53 X0 X1 X2 sF0
       grind)
    | exact superpose eq53 eq4988
    | exact resolve eq4988 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6975 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1233 eq548
    | exact resolve eq548 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq1233
  have eq7290 : ∀ X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op x y) X2) := by
    intro X1 X2
    first
    | exact superpose eq4988 eq6975
    | exact resolve eq6975 eq4988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4988 eq6975
  have eq8802 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq709 X0 X1 X2
       have i₂ := eq7290 X0 X0
       grind)
    | (have i₁ := eq709 (M.op x y) X1 X2
       have i₂ := eq7290 X1 (M.op (M.op x y) (M.op x y))
       grind)
    | exact superpose eq7290 eq709
    | exact resolve eq709 eq7290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq8850 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8802 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8802
    | (have j0 := eq8802 X0 y x
       grind)
    | exact resolve eq8802 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8802
  have eq18663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18663
    | exact resolve eq18663 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18663
  have eq18675 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18664
       have r₂ := eq28
       grind)
    | exact resolve eq18664 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18664
  have eq18677 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18675
    | exact resolve eq18675 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18675
  have eq18688 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  have eq18706 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq18677 eq5816
    | exact resolve eq5816 eq18677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18707 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18677 eq7290
    | exact resolve eq7290 eq18677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18677
  have eq18754 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18688 eq117
    | exact resolve eq117 eq18688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18688
  have eq18762 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18754
  have eq18864 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18706
    | (have j0 := eq18706 (σ y)
       grind)
    | exact resolve eq18706 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18706
  have eq19176 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18707 eq18762
    | exact resolve eq18762 eq18707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18707 eq18762
  have eq19199 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19176
  have eq19226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19199 eq18864
    | exact resolve eq18864 eq19199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18864 eq19199
  have eq19268 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19226
  have eq19295 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19268
       have r₂ := eq28
       grind)
    | exact resolve eq19268 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19268
  have eq19316 : (M.op y x) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq19295
       grind)
    | exact superpose eq19295 eq56
    | exact resolve eq56 eq19295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19317 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq213 y X0
       have i₂ := eq19295
       grind)
    | exact superpose eq19295 eq213
    | exact resolve eq213 eq19295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19323 : (k x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19295
  have eq19501 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19317 eq19316
    | exact resolve eq19316 eq19317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19316 eq19317
  have eq19587 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19501
  have eq19625 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19587
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19587
    | exact resolve eq19587 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19587
  have eq19756 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19323
       grind)
    | exact superpose eq19323 eq45
    | exact resolve eq45 eq19323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19323
  have eq20122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19756
       have i₂ := eq19625
       grind)
    | exact superpose eq19625 eq19756
    | exact resolve eq19756 eq19625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19625 eq19756
  have eq20163 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20122
  have eq20167 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq20163
    | exact resolve eq20163 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20163
  have eq20180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20167 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq20167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq20180
    | exact resolve eq20180 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20180
  have eq20194 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20183
       have r₂ := eq28
       grind)
    | exact resolve eq20183 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20183
  have eq20196 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq20194
    | exact resolve eq20194 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20194
  have eq20197 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20196
  have eq20233 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq20251 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20197 eq5816
    | exact resolve eq5816 eq20197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5816
  have eq20252 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20197 eq7290
    | exact resolve eq7290 eq20197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20197
  have eq20309 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20233 eq20167
    | exact resolve eq20167 eq20233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20167 eq20233
  have eq20311 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20309
  have eq20425 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq20251
    | (have j0 := eq20251 (σ y)
       grind)
    | exact resolve eq20251 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20251
  have eq20800 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20252 eq20311
    | exact resolve eq20311 eq20252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20252 eq20311
  have eq20825 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20800
  have eq20854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20825 eq20425
    | exact resolve eq20425 eq20825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20425 eq20825
  have eq20900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20854
  have eq20929 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20900
       have r₂ := eq28
       grind)
    | exact resolve eq20900 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20900
  have eq20949 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20929 eq28
    | exact resolve eq28 eq20929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20950 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20929 eq79
    | (have r₁ := eq79
       have r₂ := eq20929
       grind)
    | exact resolve eq79 eq20929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq20951 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20929 eq221
    | exact resolve eq221 eq20929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq20953 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20929 eq502
    | exact resolve eq502 eq20929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq20964 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20929 eq2532
    | exact resolve eq2532 eq20929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532
  have eq20971 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20950
  have eq20979 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq20951
    | exact resolve eq20951 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20951
  have eq21084 : (M.op (M.op x y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20979 eq7290
    | exact resolve eq7290 eq20979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21182 : (M.op (σ y) (M.op (M.op x y) (σ y))) = (k (M.op (M.op x y) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20964
  have eq21215 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op x y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2201 eq21182
    | exact resolve eq21182 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201 eq21182
  have eq21223 : (M.op (M.op x y) (σ y)) = (k (M.op (M.op x y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4944 eq21215
    | exact resolve eq21215 eq4944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4944 eq21215
  have eq23986 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20971 eq61
    | exact resolve eq61 eq20971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23987 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20971 eq117
    | exact resolve eq117 eq20971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20971
  have eq24004 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq23987
  have eq24018 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq24004
       have r₂ := eq20949
       grind)
    | exact resolve eq24004 eq20949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20949 eq24004
  have eq24019 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq23986
    | exact resolve eq23986 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23986
  have eq24040 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24018 eq20953
    | exact resolve eq20953 eq24018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24018
  have eq24065 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq24040
  have eq24125 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24019 eq20953
    | exact resolve eq20953 eq24019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20953 eq24019
  have eq24150 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (k x y) := by grind
  clear eq24125
  have eq24202 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24065 eq20979
    | exact resolve eq20979 eq24065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24065
  have eq24240 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24202
  have eq24269 : (M.op y x) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq24240
       grind)
    | exact superpose eq24240 eq56
    | exact resolve eq56 eq24240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24270 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq213 y X0
       have i₂ := eq24240
       grind)
    | exact superpose eq24240 eq213
    | exact resolve eq213 eq24240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24277 : (k x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24240
  have eq24552 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq24150 eq20979
    | exact resolve eq20979 eq24150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20979 eq24150
  have eq24582 : y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24552
  have eq25503 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24270 eq24269
    | exact resolve eq24269 eq24270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24269 eq24270
  have eq25634 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25503
  have eq25689 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25634
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25634
    | exact resolve eq25634 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25634
  have eq26207 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24582
       have i₂ := eq24277
       grind)
    | exact superpose eq24277 eq24582
    | exact resolve eq24582 eq24277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24277 eq24582
  have eq26210 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26207
  have eq26220 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25689
       have i₂ := eq26210
       grind)
    | exact superpose eq26210 eq25689
    | exact resolve eq25689 eq26210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25689 eq26210
  have eq26247 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq26220
  have eq26264 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26247 eq28
    | exact resolve eq28 eq26247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26273 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26247 eq2075
    | exact resolve eq2075 eq26247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq26304 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq26273
    | exact resolve eq26273 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26273
  have eq26903 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26304 eq21084
    | exact resolve eq21084 eq26304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21084 eq26304
  have eq26936 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq26903
  have eq27097 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26936 eq21223
    | exact resolve eq21223 eq26936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21223 eq26936
  have eq27150 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq27097
  have eq27630 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26247 eq27150
    | exact resolve eq27150 eq26247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26247
  have eq27631 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20929 eq27150
    | exact resolve eq27150 eq20929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20929 eq27150
  have eq27638 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq27631
  have eq27639 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq27630
  have eq28079 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27638 eq89
    | exact resolve eq89 eq27638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq27638
  have eq28112 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq28079
    | exact resolve eq28079 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28079
  have eq28126 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27639 eq61
    | exact resolve eq61 eq27639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq28127 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27639 eq117
    | exact resolve eq117 eq27639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq27639
  have eq28146 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq28127
  have eq28162 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq28146
       have r₂ := eq26264
       grind)
    | exact resolve eq28146 eq26264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26264 eq28146
  have eq28163 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq28126
    | exact resolve eq28126 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28126
  have eq29023 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq28112
       grind)
    | exact superpose eq28112 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq28112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28112
  have eq29024 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq29023
  have eq29048 : (M.op y x) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq28162
       grind)
    | exact superpose eq28162 eq56
    | exact resolve eq56 eq28162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29049 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq213 y X0
       have i₂ := eq28162
       grind)
    | exact superpose eq28162 eq213
    | exact resolve eq213 eq28162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq29056 : (k x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq28162
  have eq29242 : (M.op y y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq29024
       grind)
    | exact superpose eq29024 eq56
    | exact resolve eq56 eq29024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq45110 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29049 eq29048
    | exact resolve eq29048 eq29049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29048
  have eq45282 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq45110
  have eq45353 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45282
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq45282
    | exact resolve eq45282 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45282
  have eq46184 : x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28163
       have i₂ := eq29056
       grind)
    | exact superpose eq29056 eq28163
    | exact resolve eq28163 eq29056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28163 eq29056
  have eq46194 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq46184
  have eq46247 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45353
       have i₂ := eq46194
       grind)
    | exact superpose eq46194 eq45353
    | exact resolve eq45353 eq46194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45353 eq46194
  have eq46279 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq46247
  have eq46404 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq46279
  have eq47271 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29242 eq29049
    | exact resolve eq29049 eq29242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29049 eq29242
  have eq47315 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq47271
  have eq47346 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47315
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47315
    | exact resolve eq47315 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47315
  have eq47373 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29024
       have i₂ := eq47346
       grind)
    | exact superpose eq47346 eq29024
    | exact resolve eq29024 eq47346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29024 eq47346
  have eq47408 : y = (M.op x y) := by grind
  clear eq47373
  have eq47441 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq47408 eq21
    | exact resolve eq21 eq47408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq47446 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq47408 eq78
    | (have r₁ := eq78
       have r₂ := eq47408
       grind)
    | exact resolve eq78 eq47408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq47488 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq47408 eq212
    | exact resolve eq212 eq47408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq47512 : ∀ X0 X1 : G, (M.op y y) = (M.op y (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq47408 eq2801
    | exact resolve eq2801 eq47408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801
  have eq47523 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq47408 eq8850
    | exact resolve eq8850 eq47408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8850
  have eq47538 : y = (k x y) ∨ x = (M.op y y) := by grind
  clear eq47446
  have eq47565 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq47488
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47488
    | exact resolve eq47488 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq47488
  have eq47610 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq47441
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq47441
    | exact resolve eq47441 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47441
  have eq47618 : y = (M.op y x) := by
    first
    | exact superpose eq47408 eq47565
    | exact resolve eq47565 eq47408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47565
  have eq47622 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq47610 eq27
    | exact resolve eq27 eq47610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq51273 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq47538
       grind)
    | exact superpose eq47538 eq45
    | exact resolve eq45 eq47538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq51290 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1422 x y
       have i₂ := eq47538
       grind)
    | exact superpose eq47538 eq1422
    | (have j0 := eq1422 x y
       grind)
    | exact resolve eq1422 eq47538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47538
  have eq51297 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq51290
  have eq51308 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51297
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq51297
    | exact resolve eq51297 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51297
  have eq51319 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq47610 eq51273
    | exact resolve eq51273 eq47610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51273
  have eq51327 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq47610 eq51308
    | exact resolve eq51308 eq47610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51308
  have eq51337 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51319
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq51319
    | exact resolve eq51319 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51319
  have eq51344 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51327
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq51327
    | exact resolve eq51327 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51327
  have eq51350 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq47610 eq51337
    | exact resolve eq51337 eq47610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51337
  have eq51357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq47622 eq51344
    | exact resolve eq51344 eq47622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51344
  have eq51365 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq51357
       have r₂ := eq28
       grind)
    | exact resolve eq51357 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51357
  have eq51373 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51365
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq51365
    | exact resolve eq51365 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51365
  have eq51381 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq47610 eq51373
    | exact resolve eq51373 eq47610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51373
  have eq51389 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51381
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq51381
    | exact resolve eq51381 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51381
  have eq51478 : (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by grind
  have eq51497 : (M.op (σ (M.op x y)) (σ x)) = (M.op (M.op x y) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq51389 eq7290
    | exact resolve eq7290 eq51389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7290
  have eq51513 : (M.op (σ (M.op x y)) (σ x)) = (M.op y (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq47408 eq51497
    | exact resolve eq51497 eq47408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51497
  have eq52394 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq51478 eq51350
    | exact resolve eq51350 eq51478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51350 eq51478
  have eq52404 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq52394
  have eq52537 : (σ (M.op x y)) = (M.op y (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq51513 eq52404
    | exact resolve eq52404 eq51513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51513 eq52404
  have eq52569 : (σ (M.op x y)) = (M.op y (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq52537
  have eq52605 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq52569 eq47523
    | exact resolve eq47523 eq52569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47523 eq52569
  have eq52667 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq52605 eq51389
    | exact resolve eq51389 eq52605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51389 eq52605
  have eq52697 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq52667
  have eq52783 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq47512 y y
       have i₂ := eq52697
       grind)
    | exact superpose eq52697 eq47512
    | exact resolve eq47512 eq52697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47512 eq52697
  have eq52785 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq52783
       have i₂ := eq47618
       grind)
    | exact superpose eq47618 eq52783
    | exact resolve eq52783 eq47618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52783
  have eq52849 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq52785 eq29
    | exact resolve eq29 eq52785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52785
  have eq53059 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq52849
    | exact resolve eq52849 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq52849
  have eq53118 : x = (M.op x y) := by
    first
    | (have r₁ := eq53059
       have r₂ := eq46404
       grind)
    | exact resolve eq53059 eq46404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46404 eq53059
  have eq53119 : x = y := by
    first
    | exact superpose eq47408 eq53118
    | exact resolve eq53118 eq47408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47408 eq53118
  have eq53121 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq53119
       grind)
    | exact superpose eq53119 eq25
    | exact resolve eq25 eq53119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq53234 : x = (M.op x x) := by
    first
    | (have i₁ := eq47618
       have i₂ := eq53119
       grind)
    | exact superpose eq53119 eq47618
    | exact resolve eq47618 eq53119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47618 eq53119
  have eq53341 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq47610 eq53121
    | exact resolve eq53121 eq47610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47610 eq53121
  have eq53409 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53341
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53341
    | exact resolve eq53341 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53341
  have eq53586 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq53409 eq47622
    | exact resolve eq47622 eq53409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47622
  have eq53732 : (k x x) = (M.op x x) := by grind
  have eq53775 : x = (k x x) := by
    first
    | (have i₁ := eq53732
       have i₂ := eq53234
       grind)
    | exact superpose eq53234 eq53732
    | exact resolve eq53732 eq53234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53234 eq53732
  have eq53926 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1422 x x
       have i₂ := eq53775
       grind)
    | exact superpose eq53775 eq1422
    | (have j0 := eq1422 x x
       grind)
    | exact resolve eq1422 eq53775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq53775
  have eq53939 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq53926
  have eq53940 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq53939
  have eq53954 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq53940
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53940
    | exact resolve eq53940 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq53940
  have eq53972 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq53409 eq53954
    | exact resolve eq53954 eq53409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53409 eq53954
  have eq53990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53586 eq53972
    | exact resolve eq53972 eq53586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53586 eq53972
  have eq54007 : False := by grind
  exact eq54007

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = (M.op X2 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = (M.op X2 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq36 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq224 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1198 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1199 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1204 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1199 X0 X1
       have j1 := eq224 X0 X1
       grind)
    | (have r₁ := eq1199 X0 X1
       have r₂ := eq224 X0 X1
       grind)
    | (have r₁ := eq1199 X1 X1
       have r₂ := eq224 X1 X1
       grind)
    | exact resolve eq1199 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq1199
  have eq1845 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1204 (σ X0) (σ X1)
       grind)
    | exact superpose eq1204 eq15
    | exact resolve eq15 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1848 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1845 X0 X1
       have i₂ := eq1204 X0 X1
       grind)
    | exact superpose eq1204 eq1845
    | exact resolve eq1845 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204 eq1845
  have eq1852 : False := by grind
  exact eq1852

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyx_pxy_Equation4419 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq58 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
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
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq78
    | exact resolve eq78 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq90 : x ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y x) := by
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
  have eq91 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 y X0 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq53
    | exact resolve eq53 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq780 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq59 eq53
    | exact resolve eq53 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq59
  have eq883 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq229 eq780
    | (have j0 := eq780 X0 (σ x)
       grind)
    | exact resolve eq780 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq884 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq779 X0 x
       have i₂ := eq218 x X0
       grind)
    | (have i₁ := eq779 x x
       have i₂ := eq218 X0 x
       grind)
    | exact superpose eq218 eq779
    | (have j0 := eq779 X0 x
       grind)
    | exact resolve eq779 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq2259 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq229 eq883
    | exact resolve eq883 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq883
  have eq2390 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq884 y
       have i₂ := eq218 sF0 y
       grind)
    | exact superpose eq218 eq884
    | exact resolve eq884 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq884
  have eq10740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq10740
    | exact resolve eq10740 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10740
  have eq10744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq10741
       have r₂ := eq28
       grind)
    | exact resolve eq10741 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10741
  have eq10746 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq10744
    | exact resolve eq10744 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10744
  have eq10748 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10746 eq28
    | exact resolve eq28 eq10746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10749 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10746 eq91
    | (have r₁ := eq91
       have r₂ := eq10746
       grind)
    | exact resolve eq91 eq10746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq10758 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10746 eq2259
    | exact resolve eq2259 eq10746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq10769 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10749
  have eq10770 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10769
  have eq10774 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq10758
    | exact resolve eq10758 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10758
  have eq10783 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10746 eq10774
    | exact resolve eq10774 eq10746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10746 eq10774
  have eq10803 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10783
  have eq10901 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10770 eq80
    | exact resolve eq80 eq10770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq10770
  have eq10905 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10901
  have eq10913 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10905 eq10803
    | exact resolve eq10803 eq10905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10803 eq10905
  have eq10933 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10913
  have eq10949 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq10933
       have r₂ := eq10748
       grind)
    | exact resolve eq10933 eq10748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10748 eq10933
  have eq10959 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10949 eq30
    | exact resolve eq30 eq10949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10949
  have eq10996 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq10959
    | exact resolve eq10959 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10959
  have eq10997 : x = (M.op x y) ∨ x = y := by grind
  clear eq10996
  have eq11005 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq10997 eq21
    | exact resolve eq21 eq10997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11007 : x ≠ x ∨ x = y ∨ (k x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10997 eq90
    | (have r₁ := eq90
       have r₂ := eq10997
       grind)
    | exact resolve eq90 eq10997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq11026 : (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq10997 eq2390
    | exact resolve eq2390 eq10997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390
  have eq11043 : x ≠ x ∨ x = y ∨ (k x y) = (M.op y x) := by grind
  clear eq11007
  have eq11044 : (k x y) = (M.op y x) ∨ x = y := by grind
  clear eq11043
  have eq11054 : (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq11026
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11026
    | exact resolve eq11026 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11026
  have eq11071 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq11005
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11005
    | exact resolve eq11005 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11005
  have eq11123 : x = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq10997 eq11054
    | exact resolve eq11054 eq10997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10997 eq11054
  have eq11140 : x = (M.op y x) ∨ x = y := by grind
  clear eq11123
  have eq11311 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11044
       grind)
    | exact superpose eq11044 eq49
    | exact resolve eq49 eq11044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq11044
  have eq12695 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq11311
       have i₂ := eq11140
       grind)
    | exact superpose eq11140 eq11311
    | exact resolve eq11311 eq11140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11140 eq11311
  have eq12721 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq12695
  have eq12728 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12721
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12721
    | exact resolve eq12721 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12721
  have eq12752 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12728 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12728
  have eq12753 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12752
  have eq12765 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12753
    | exact resolve eq12753 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12753
  have eq12883 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12765 eq28
    | exact resolve eq28 eq12765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12765
  have eq12923 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12883
       have r₂ := eq11071
       grind)
    | exact resolve eq12883 eq11071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11071 eq12883
  have eq12929 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq12923 eq30
    | exact resolve eq30 eq12923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12923
  have eq12982 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq12929
    | exact resolve eq12929 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12929
  have eq12983 : x = y := by grind
  clear eq12982
  have eq12992 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq12983
       grind)
    | exact superpose eq12983 eq19
    | exact resolve eq19 eq12983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq12993 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq12983
       grind)
    | exact superpose eq12983 eq25
    | exact resolve eq25 eq12983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12983
  have eq13035 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12993
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12993
    | exact resolve eq12993 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq12993
  have eq13039 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13035 eq27
    | exact resolve eq27 eq13035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq13035
  have eq13139 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13039 eq71
    | exact resolve eq71 eq13039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq13039
  have eq13176 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13139
       have i₂ := eq12992
       grind)
    | exact superpose eq12992 eq13139
    | exact resolve eq13139 eq12992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12992 eq13139
  have eq13187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13176 eq15
    | exact resolve eq15 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13176
  have eq13230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq13187
    | exact resolve eq13187 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq13187
  have eq13239 : False := by grind
  exact eq13239

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation442 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq613 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq3372 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq616 x y
       grind)
    | exact superpose eq616 eq16
    | (have j1 := eq616 x y
       grind)
    | exact resolve eq16 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3387 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq616 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4801 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq613
    | exact resolve eq613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq4867 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4801 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4801
    | (have j0 := eq4801 X0 X1
       grind)
    | exact resolve eq4801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4801
  have eq34830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3372
       have i₂ := eq4867 y x
       grind)
    | exact superpose eq4867 eq3372
    | (have j1 := eq4867 (σ x) (σ y)
       grind)
    | (have r₁ := eq3372
       have r₂ := eq4867 y x
       grind)
    | (have r₁ := eq3372
       have r₂ := eq4867 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3372
       have r₂ := eq4867 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3372 eq4867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4867
  have eq34831 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq34830
  have eq43820 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3387 X1 X0
       have i₂ := eq616 X0 X1
       grind)
    | exact superpose eq616 eq3387
    | (have j0 := eq3387 X0 X1
       have j1 := eq616 X0 X1
       grind)
    | (have r₁ := eq3387 X0 X0
       have r₂ := eq616 X0 X0
       grind)
    | exact resolve eq3387 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq43827 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq43820 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43820
  have eq43833 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq43827 X0 X1
       have j1 := eq3387 X0 X1
       grind)
    | (have r₁ := eq43827 X0 X1
       have r₂ := eq3387 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq43827 X0 X1
       have r₂ := eq3387 (k X1 X0) (k X0 X1)
       grind)
    | (have r₁ := eq43827 X0 X1
       have r₂ := eq3387 X0 X1
       grind)
    | exact resolve eq43827 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387 eq43827
  have eq44024 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq43833 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq43833
    | (have j0 := eq43833 (τ X0) (τ X1)
       grind)
    | exact resolve eq43833 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq43833
  have eq44087 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44024 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq44024
    | (have j0 := eq44024 X0 X1
       grind)
    | exact resolve eq44024 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq44024
  have eq44161 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44087 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq44087
    | (have j0 := eq44087 X0 X1
       grind)
    | exact resolve eq44087 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44087
  have eq44211 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44161 X1 X0
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq44161
    | (have j0 := eq44161 X0 X1
       grind)
    | (have r₁ := eq44161 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq44161 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44161
  have eq44259 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44211 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq44211
    | (have j0 := eq44211 X0 X1
       grind)
    | exact resolve eq44211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44211
  have eq44304 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44259 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44259
    | (have j0 := eq44259 X0 X1
       grind)
    | exact resolve eq44259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44259
  have eq44334 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44304 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44304
    | (have j0 := eq44304 X0 X1
       grind)
    | exact resolve eq44304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44304
  have eq44352 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44334 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44334
    | (have j0 := eq44334 X0 X1
       grind)
    | exact resolve eq44334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44334
  have eq91208 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34831
       grind)
    | exact superpose eq34831 eq16
    | exact resolve eq16 eq34831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34831
  have eq91209 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq91208
       have r₂ := eq22 x
       grind)
    | exact resolve eq91208 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91208
  have eq91212 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq91209
       grind)
    | exact superpose eq91209 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq91209
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq91209
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq91209
       grind)
    | exact resolve eq13 eq91209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91209
  have eq91306 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq91212
  have eq99119 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91306
       grind)
    | exact superpose eq91306 eq16
    | exact resolve eq16 eq91306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91306
  have eq99120 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq99119
       have r₂ := eq22 x
       grind)
    | exact resolve eq99119 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99119
  have eq99121 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3372
       have i₂ := eq99120
       grind)
    | exact superpose eq99120 eq3372
    | exact resolve eq3372 eq99120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372 eq99120
  have eq99136 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq99121
  have eq99137 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq99136
  have eq99161 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq99137
       grind)
    | exact superpose eq99137 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq99137
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq99137
       grind)
    | exact resolve eq13 eq99137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99162 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq99137
       grind)
    | exact superpose eq99137 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq99137
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq99137
       grind)
    | exact resolve eq13 eq99137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99137
  have eq99257 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq99162
  have eq99258 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq99257
  have eq99259 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq99161
  have eq99260 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq99259
  have eq99297 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq99258
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq99258
    | exact resolve eq99258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99258
  have eq99298 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq99260
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq99260
    | exact resolve eq99260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99260
  have eq99300 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99297
       grind)
    | exact superpose eq99297 eq16
    | exact resolve eq16 eq99297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99496 : (σ (k x y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq99297
       have i₂ := eq99298
       grind)
    | exact superpose eq99298 eq99297
    | exact resolve eq99297 eq99298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99297 eq99298
  have eq99631 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq99496
  have eq99686 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq99631
       grind)
    | exact superpose eq99631 eq10
    | exact resolve eq10 eq99631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99631
  have eq99904 : x = y ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq99686
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq99686
    | exact resolve eq99686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99686
  have eq99906 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99904
       grind)
    | exact superpose eq99904 eq16
    | exact resolve eq16 eq99904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99904
  have eq99907 : (σ (k x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq99906
       have r₂ := eq22 x
       grind)
    | exact resolve eq99906 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99906
  have eq99922 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq99907
       grind)
    | exact superpose eq99907 eq10
    | exact resolve eq10 eq99907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99907
  have eq100142 : (k x y) = (k y x) := by
    first
    | (have i₁ := eq99922
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq99922
    | exact resolve eq99922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99922
  have eq100175 : (k x y) ≠ (k x y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44352 x y
       have i₂ := eq100142
       grind)
    | exact superpose eq100142 eq44352
    | (have j0 := eq44352 x y
       grind)
    | (have r₁ := eq44352 x y
       have r₂ := eq100142
       grind)
    | (have r₁ := eq44352 y x
       have r₂ := eq100142
       grind)
    | exact resolve eq44352 eq100142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44352 eq100142
  have eq100195 : x = y ∨ (M.op x y) = (M.op y x) := by grind
  clear eq100175
  have eq100202 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100195
       grind)
    | exact superpose eq100195 eq16
    | exact resolve eq16 eq100195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100195
  have eq100203 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq100202
       have r₂ := eq22 x
       grind)
    | exact resolve eq100202 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100202
  have eq100206 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq100203
       grind)
    | exact superpose eq100203 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq100203
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq100203
       grind)
    | exact resolve eq13 eq100203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100203
  have eq100301 : x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq100206
  have eq100408 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100301
       grind)
    | exact superpose eq100301 eq16
    | exact resolve eq16 eq100301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100301
  have eq100410 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq100408
       have r₂ := eq22 x
       grind)
    | exact resolve eq100408 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100408
  have eq100416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq99300
       have i₂ := eq100410
       grind)
    | exact superpose eq100410 eq99300
    | exact resolve eq99300 eq100410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99300 eq100410
  have eq100431 : (σ x) = (σ y) := by grind
  clear eq100416
  have eq100432 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100431
       grind)
    | exact superpose eq100431 eq16
    | exact resolve eq16 eq100431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100433 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq100431
       grind)
    | exact superpose eq100431 eq10
    | exact resolve eq10 eq100431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100431
  have eq100651 : x = y := by
    first
    | (have i₁ := eq100433
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq100433
    | exact resolve eq100433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100433
  have eq100652 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq100432
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq100432
    | exact resolve eq100432 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq100432
  have eq100653 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq100652
       have i₂ := eq100651
       grind)
    | exact superpose eq100651 eq100652
    | exact resolve eq100652 eq100651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100651 eq100652
  have eq100654 : False := by grind
  exact eq100654

/-- `Equation4425`: `x ◇ (x ◇ y) = (z ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation4425 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4425 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4425.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X2) := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X2 X3 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq67 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq67
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67
    | exact resolve eq67 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq71
    | exact resolve eq71 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq50
    | (have j0 := eq50 X0 X1 x y
       grind)
    | exact resolve eq50 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq492 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq470 X0 (M.op X0 x)
       have i₂ := eq470 X0 x
       grind)
    | (have i₁ := eq470 x (M.op x y)
       have i₂ := eq470 X0 x
       grind)
    | exact superpose eq470 eq470
    | exact resolve eq470 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq470
    | (have j0 := eq470 (σ x) (σ y)
       grind)
    | exact resolve eq470 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq470 x x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq470
    | (have j1 := eq14 x y X0
       grind)
    | exact resolve eq470 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) (M.op x (M.op x y))) := by grind
  have eq770 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq63 X1 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq775 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq770 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq784 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq775 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq775 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq775 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq775 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq802 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq784 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq784
    | (have j0 := eq784 X0 X1
       grind)
    | exact resolve eq784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq6813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq73 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq6814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq6813
    | exact resolve eq6813 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6813
  have eq6825 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq6814
       have r₂ := eq28
       grind)
    | exact resolve eq6814 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6814
  have eq6827 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq6825
    | exact resolve eq6825 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6825
  have eq6830 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq6827
  have eq6852 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6830 eq58
    | exact resolve eq58 eq6830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq6830
  have eq6871 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq6852
    | exact resolve eq6852 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6852
  have eq9781 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq6871
       grind)
    | exact superpose eq6871 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq6871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6871
  have eq9782 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9781
  have eq9787 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9782
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9782
    | exact resolve eq9782 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9782
  have eq9788 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9787
  have eq9811 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq9816 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq470 x x
       have i₂ := eq9788
       grind)
    | exact superpose eq9788 eq470
    | exact resolve eq470 eq9788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9788
  have eq9822 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9816
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9816
    | exact resolve eq9816 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9816
  have eq10087 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq802 x y
       have i₂ := eq9811
       grind)
    | exact superpose eq9811 eq802
    | (have j0 := eq802 x y
       grind)
    | exact resolve eq802 eq9811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq9811
  have eq10092 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10087
  have eq10093 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10092
  have eq10096 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10093
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10093
    | exact resolve eq10093 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10093
  have eq10106 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10096
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10096
    | exact resolve eq10096 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10096
  have eq10123 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9822 eq492
    | exact resolve eq492 eq9822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10124 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9822 eq629
    | exact resolve eq629 eq9822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9822
  have eq10688 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10106 eq470
    | exact resolve eq470 eq10106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10106
  have eq10694 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10688
    | exact resolve eq10688 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10688
  have eq10716 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10123 eq470
    | exact resolve eq470 eq10123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10123
  have eq11622 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10124 eq772
    | (have j0 := eq772 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq772 eq10124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq10124
  have eq11625 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11622
  have eq11626 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11625
  have eq11634 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11626
    | exact resolve eq11626 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11626
  have eq12223 : (M.op x (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11634 eq502
    | exact resolve eq502 eq11634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14159 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10716 eq10694
    | exact resolve eq10694 eq10716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10694 eq10716
  have eq14197 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14159 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14159
  have eq14367 : (σ (M.op x y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12223 eq11634
    | exact resolve eq11634 eq12223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11634 eq12223
  have eq14380 : (σ (M.op x y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14367
  have eq14419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14380 eq14197
    | exact resolve eq14197 eq14380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14197 eq14380
  have eq14430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14419
  have eq14456 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14430
       have r₂ := eq28
       grind)
    | exact resolve eq14430 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14430
  have eq14465 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14456 eq499
    | exact resolve eq499 eq14456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq14475 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14465
    | exact resolve eq14465 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14465
  have eq14486 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14475 eq629
    | exact resolve eq629 eq14475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14475
  have eq14579 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14456 eq14486
    | exact resolve eq14486 eq14456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14456 eq14486
  have eq14605 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14579
  have eq14663 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14605 eq107
    | exact resolve eq107 eq14605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq14605
  have eq14709 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq14663
    | exact resolve eq14663 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14663
  have eq14806 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq14709
       grind)
    | exact superpose eq14709 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq14709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14709
  have eq14807 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq14806
  have eq14854 : (M.op x (M.op x y)) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq502 y
       have i₂ := eq14807
       grind)
    | exact superpose eq14807 eq502
    | exact resolve eq502 eq14807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq19168 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14807
       have i₂ := eq14854
       grind)
    | exact superpose eq14854 eq14807
    | exact resolve eq14807 eq14854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14807 eq14854
  have eq19181 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq19168
  have eq19254 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19181 eq470
    | exact resolve eq470 eq19181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19181
  have eq19299 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19254
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19254
    | exact resolve eq19254 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19254
  have eq19300 : y = (M.op x y) := by grind
  clear eq19299
  have eq19311 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq19300 eq21
    | exact resolve eq21 eq19300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq19369 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19300 eq492
    | exact resolve eq492 eq19300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq19370 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq19300 eq629
    | exact resolve eq629 eq19300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq19392 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq19370
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19370
    | exact resolve eq19370 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19370
  have eq19393 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq19369 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19369
    | (have j0 := eq19369 X0
       grind)
    | exact resolve eq19369 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19369
  have eq19449 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19311
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19311
    | exact resolve eq19311 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19311
  have eq19455 : y = (k y y) := by
    first
    | exact superpose eq19300 eq19392
    | exact resolve eq19392 eq19300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19392
  have eq19456 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq19300 eq19393
    | exact resolve eq19393 eq19300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19393
  have eq19461 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq19449 eq27
    | exact resolve eq27 eq19449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq19606 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19455
       grind)
    | exact superpose eq19455 eq92
    | exact resolve eq92 eq19455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq19455
  have eq19651 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19449 eq19606
    | exact resolve eq19606 eq19449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19606
  have eq19668 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq19651
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19651
    | exact resolve eq19651 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq19651
  have eq19684 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19449 eq19668
    | exact resolve eq19668 eq19449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19449 eq19668
  have eq20226 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19684 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq19684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19684
  have eq20227 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq20226
  have eq20303 : (M.op x (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20227 eq470
    | exact resolve eq470 eq20227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq20308 : (σ (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq20227 eq20303
    | exact resolve eq20303 eq20227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20227 eq20303
  have eq20316 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq19300 eq20308
    | exact resolve eq20308 eq19300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20308
  have eq20324 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq20316
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20316
    | exact resolve eq20316 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20316
  have eq20332 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq19300 eq20324
    | exact resolve eq20324 eq19300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19300 eq20324
  have eq20409 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq20332 eq19461
    | exact resolve eq19461 eq20332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19461
  have eq20412 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20409
       have i₂ := eq19456 sF2
       grind)
    | exact superpose eq19456 eq20409
    | exact resolve eq20409 eq19456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19456 eq20409
  have eq20629 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq20412 eq28
    | exact resolve eq28 eq20412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20412
  have eq20666 : False := by grind
  exact eq20666

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxx_x_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op y (M.op y (M.op x y)))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  clear eq36
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
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq95 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  clear eq73
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq862 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq94 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq863 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq864 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq2975 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq864 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq864
    | (have j0 := eq864 (τ X0)
       grind)
    | exact resolve eq864 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq864
  have eq2983 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2975 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2975
    | (have j0 := eq2975 X0
       grind)
    | exact resolve eq2975 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975
  have eq2989 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2983 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2983
    | (have j0 := eq2983 X0
       grind)
    | exact resolve eq2983 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2983
  have eq3882 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq95 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 x
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3894 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3882
  have eq3899 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3894
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3894
    | exact resolve eq3894 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3894
  have eq3917 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3899
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3899 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3899
  have eq3924 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3917 eq49
    | exact resolve eq49 eq3917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3917
  have eq13349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq13350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13349
    | exact resolve eq13349 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13349
  have eq13361 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq13350
       have r₂ := eq27
       grind)
    | exact resolve eq13350 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13350
  have eq13363 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13361
    | exact resolve eq13361 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13361
  have eq13577 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13363 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13363
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13363
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13363
       grind)
    | exact resolve eq12 eq13363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13363
  have eq13593 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq13577
  have eq13594 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13593
    | exact resolve eq13593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13593
  have eq13595 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq13594
  have eq13600 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13595 eq83
    | exact resolve eq83 eq13595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq13595
  have eq13627 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq13600
    | exact resolve eq13600 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13600
  have eq14648 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq13627
       grind)
    | exact superpose eq13627 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq13627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13627
  have eq14658 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14648
  have eq14666 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14658
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14658
    | exact resolve eq14658 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14658
  have eq14667 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14666
  have eq14692 : x ≠ x ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14667
       grind)
    | exact superpose eq14667 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14667
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14667
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14667
       grind)
    | exact resolve eq12 eq14667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14694 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq14667
       grind)
    | exact superpose eq14667 eq14
    | exact resolve eq14 eq14667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14708 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14692
  have eq14709 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14708
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14708
    | exact resolve eq14708 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14708
  have eq14710 : y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14709
  have eq14795 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq863 x y
       have i₂ := eq14710
       grind)
    | exact superpose eq14710 eq863
    | (have j0 := eq863 x y
       grind)
    | exact resolve eq863 eq14710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863 eq14710
  have eq14800 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14795
  have eq14805 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14800
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14800
    | exact resolve eq14800 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14800
  have eq14818 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14805
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14805
    | exact resolve eq14805 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14805
  have eq14826 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14818
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14818
    | exact resolve eq14818 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14818
  have eq14831 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14826
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14826
    | exact resolve eq14826 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14826
  have eq14836 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14831
    | exact resolve eq14831 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14831
  have eq14837 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14836
  have eq14960 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14837 eq14
    | exact resolve eq14 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16756 : ∀ X0 : G, (M.op X0 x) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq14694 x
       grind)
    | exact superpose eq14694 eq14
    | exact resolve eq14 eq14694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14694
  have eq16900 : x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14667
       have i₂ := eq16756 y
       grind)
    | exact superpose eq16756 eq14667
    | exact resolve eq14667 eq16756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14667
  have eq16903 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq16900
  have eq16940 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16903 eq51
    | exact resolve eq51 eq16903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq16903
  have eq21744 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14960 eq14
    | exact resolve eq14 eq14960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14960
  have eq21984 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21744 eq14837
    | exact resolve eq14837 eq21744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14837 eq21744
  have eq21989 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq21984
  have eq23320 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16940 eq14
    | exact resolve eq14 eq16940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16940
  have eq23488 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq23320
    | (have j0 := eq23320 (σ x)
       grind)
    | exact resolve eq23320 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23320
  have eq23643 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq23488 eq21989
    | exact resolve eq21989 eq23488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21989 eq23488
  have eq23644 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq23643
  have eq23650 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq23644 eq29
    | exact resolve eq29 eq23644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23644
  have eq23833 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq23650
    | exact resolve eq23650 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23650
  have eq23834 : y = (M.op x y) ∨ x = y := by grind
  clear eq23833
  have eq23846 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq23834 eq50
    | exact resolve eq50 eq23834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq23848 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq23834 eq63
    | (have r₁ := eq63
       have r₂ := eq23834
       grind)
    | exact resolve eq63 eq23834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23910 : (k y x) = (M.op y y) ∨ x = y := by grind
  clear eq23848
  have eq25844 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq23846 y
       grind)
    | exact superpose eq23846 eq14
    | exact resolve eq14 eq23846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23846
  have eq26009 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq25844 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25844
    | (have j0 := eq25844 x
       grind)
    | exact resolve eq25844 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25844
  have eq26379 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq26009 eq23834
    | exact resolve eq23834 eq26009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23834 eq26009
  have eq26398 : x = y := by grind
  clear eq26379
  have eq26491 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26398
       grind)
    | exact superpose eq26398 eq18
    | exact resolve eq18 eq26398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq26492 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq26398
       grind)
    | exact superpose eq26398 eq24
    | exact resolve eq24 eq26398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq26620 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26492
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26492
    | exact resolve eq26492 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26492
  have eq26658 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26620 eq26
    | exact resolve eq26 eq26620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq26883 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16756 x
       have i₂ := eq26491
       grind)
    | exact superpose eq26491 eq16756
    | exact resolve eq16756 eq26491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16756
  have eq26910 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26883
       have i₂ := eq26398
       grind)
    | exact superpose eq26398 eq26883
    | exact resolve eq26883 eq26398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26883
  have eq26911 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26910
  have eq26917 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26620 eq26911
    | exact resolve eq26911 eq26620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26620 eq26911
  have eq26930 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26658 eq3924
    | exact resolve eq3924 eq26658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3924 eq26658
  have eq27469 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2989 x
       have i₂ := eq26930
       grind)
    | exact superpose eq26930 eq2989
    | (have j0 := eq2989 x
       grind)
    | exact resolve eq2989 eq26930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2989
  have eq27497 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27469
       have i₂ := eq26491
       grind)
    | exact superpose eq26491 eq27469
    | exact resolve eq27469 eq26491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27469
  have eq27958 : x ≠ (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26917 eq27497
    | exact resolve eq27497 eq26917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26917 eq27497
  have eq27962 : x ≠ (τ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq27958
  have eq27963 : x = (M.op x y) := by
    first
    | (have r₁ := eq27962
       have r₂ := eq28
       grind)
    | exact resolve eq27962 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq27962
  have eq27965 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq27963 eq20
    | exact resolve eq20 eq27963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27969 : x ≠ y ∨ (k y x) = (M.op y y) := by
    first
    | exact superpose eq27963 eq63
    | exact resolve eq63 eq27963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq28110 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq27969
       have r₂ := eq23910
       grind)
    | exact resolve eq27969 eq23910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23910 eq27969
  have eq28114 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq27965
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27965
    | exact resolve eq27965 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27965
  have eq28168 : (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq28110
       have i₂ := eq26398
       grind)
    | exact superpose eq26398 eq28110
    | exact resolve eq28110 eq26398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26398 eq28110
  have eq28225 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq28168
       have i₂ := eq26491
       grind)
    | exact superpose eq26491 eq28168
    | exact resolve eq28168 eq26491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26491 eq28168
  have eq28273 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq28225
       have i₂ := eq26930
       grind)
    | exact superpose eq26930 eq28225
    | exact resolve eq28225 eq26930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26930 eq28225
  have eq28314 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27963 eq28273
    | exact resolve eq28273 eq27963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27963 eq28273
  have eq28701 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28314 eq15
    | exact resolve eq15 eq28314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28314
  have eq28761 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28701
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28701
    | exact resolve eq28701 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28701
  have eq28781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28114 eq28761
    | exact resolve eq28761 eq28114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28114 eq28761
  have eq28799 : False := by grind
  exact eq28799

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  clear eq18
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq117 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (M.op X0 (M.op X0 (M.op X1 X0))) X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq132 X0 X1 X2
       have i₂ := eq22 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq22 eq132
    | exact resolve eq132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq155 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op X0 (M.op X0 (M.op X1 X0)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq147 X0 X1 X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq147
    | exact resolve eq147 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq159 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq155 X0 X1 X2
       have i₂ := eq22 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq22 eq155
    | exact resolve eq155 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq162 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X0 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq159 X0 X1 X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq159
    | exact resolve eq159 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq252 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) (M.op (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) X1
       have i₂ := eq47 X0 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq47 eq117
    | exact resolve eq117 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq277 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) (τ (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 X1
       have i₂ := eq67 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq67 eq252
    | exact resolve eq252 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq289 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 X1
       have i₂ := eq47 X0 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq47 eq277
    | exact resolve eq277 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq297 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq67 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq67 eq289
    | exact resolve eq289 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq289
  have eq304 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq297 X0 X1
       have i₂ := eq47 X0 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq47 eq297
    | exact resolve eq297 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq297
  have eq320 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq16
    | (have j1 := eq94 x y
       grind)
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1920 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq320
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq320
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq320
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq320
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq1921 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1920
  have eq22788 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1921
       grind)
    | exact superpose eq1921 eq16
    | exact resolve eq16 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq22789 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22788
       have r₂ := eq22 x
       grind)
    | exact resolve eq22788 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22788
  have eq22790 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq22789
       grind)
    | exact superpose eq22789 eq9
    | exact resolve eq9 eq22789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22791 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq22789
       grind)
    | exact superpose eq22789 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22789
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22789
       grind)
    | exact resolve eq13 eq22789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22789
  have eq22826 : x = y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22791
  have eq68908 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 ∨ (σ x) = (σ y) ∨ (M.op X1 (M.op y (M.op y y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq22790 X1
       grind)
    | exact superpose eq22790 eq9
    | (have j1 := eq22790 X1
       grind)
    | exact resolve eq9 eq22790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22790
  have eq69012 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (M.op X0 (M.op (σ y) (σ (M.op y y)))) = X0 ∨ (M.op X1 (M.op y (M.op y y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68908 X0 X1
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq68908
    | (have j0 := eq68908 X0 X1
       grind)
    | exact resolve eq68908 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68908
  have eq110100 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22826
       grind)
    | exact superpose eq22826 eq16
    | exact resolve eq16 eq22826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22826
  have eq110101 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq110100
       have r₂ := eq22 x
       grind)
    | exact resolve eq110100 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110100
  have eq110107 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq330 x y
       have i₂ := eq110101
       grind)
    | exact superpose eq110101 eq330
    | (have j0 := eq330 x y
       grind)
    | exact resolve eq330 eq110101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq110101
  have eq110130 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq110107
  have eq474606 : ∀ X0 X1 : G, y = (τ (σ x)) ∨ (M.op X0 (M.op (σ y) (σ (M.op y y)))) = X0 ∨ (M.op X1 (M.op y (M.op y y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 y
       have i₂ := eq69012 X0 X1
       grind)
    | exact superpose eq69012 eq10
    | (have j1 := eq69012 X0 X1
       grind)
    | exact resolve eq10 eq69012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69012
  have eq475056 : ∀ X0 X1 : G, x = y ∨ (M.op X0 (M.op (σ y) (σ (M.op y y)))) = X0 ∨ (M.op X1 (M.op y (M.op y y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq474606 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq474606
    | (have j0 := eq474606 X0 X1
       grind)
    | exact resolve eq474606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474606
  have eq476150 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (M.op (σ y) (σ (M.op y y)))) = X0 ∨ (M.op X1 (M.op y (M.op y y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq475056 X0 X1
       grind)
    | exact superpose eq475056 eq16
    | (have j1 := eq475056 X0 X1
       grind)
    | exact resolve eq16 eq475056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475056
  have eq476221 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (σ (M.op y y)))) = X0 ∨ (M.op X1 (M.op y (M.op y y))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq476150 X0 X1
       grind)
    | (have r₁ := eq476150 X0 X1
       have r₂ := eq22 x
       grind)
    | exact resolve eq476150 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476150
  have eq476667 : ∀ X0 X1 : G, (M.op X0 (τ (σ y))) = X0 ∨ (M.op X1 (M.op y (M.op y y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq304 y X0
       have i₂ := eq476221 (σ y) X1
       grind)
    | exact superpose eq476221 eq304
    | (have j1 := eq476221 X0 X1
       grind)
    | exact resolve eq304 eq476221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq476221
  have eq476788 : ∀ X0 X1 : G, (M.op X0 y) = X0 ∨ (M.op X1 (M.op y (M.op y y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq476667 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq476667
    | (have j0 := eq476667 X0 X1
       grind)
    | exact resolve eq476667 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476667
  have eq480389 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op y y))) = X2 ∨ (M.op X1 (M.op y (M.op y X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 y X0
       have i₂ := eq476788 X0 X2
       grind)
    | exact superpose eq476788 eq9
    | (have j1 := eq476788 X0 X2
       grind)
    | exact resolve eq9 eq476788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476788
  have eq502557 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have j0 := eq480389 y X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480389
  have eq502558 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have j0 := eq502557 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502557
  have eq503118 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq502558 y
       grind)
    | exact superpose eq502558 eq9
    | exact resolve eq9 eq502558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503121 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq162 y y X0
       have i₂ := eq502558 y
       grind)
    | exact superpose eq502558 eq162
    | exact resolve eq162 eq502558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq502558
  have eq507674 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq110130
       have i₂ := eq503118 y
       grind)
    | exact superpose eq503118 eq110130
    | exact resolve eq110130 eq503118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110130
  have eq507699 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq507674
  have eq507753 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq507699
       have i₂ := eq503121 (σ x)
       grind)
    | exact superpose eq503121 eq507699
    | exact resolve eq507699 eq503121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503121 eq507699
  have eq507754 : (σ x) = (σ y) := by grind
  clear eq507753
  have eq508174 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq507754
       grind)
    | exact superpose eq507754 eq16
    | exact resolve eq16 eq507754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508183 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq507754
       grind)
    | exact superpose eq507754 eq22
    | exact resolve eq22 eq507754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508722 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq508183
       have i₂ := eq503118 y
       grind)
    | exact superpose eq503118 eq508183
    | exact resolve eq508183 eq503118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508183
  have eq508726 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq508174
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq508174
    | exact resolve eq508174 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508174
  have eq508814 : (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq508722
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq508722
    | exact resolve eq508722 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq508722
  have eq508815 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq508726
       have i₂ := eq503118 x
       grind)
    | exact superpose eq503118 eq508726
    | exact resolve eq508726 eq503118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503118 eq508726
  have eq508903 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq508814
       have i₂ := eq507754
       grind)
    | exact superpose eq507754 eq508814
    | exact resolve eq508814 eq507754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507754 eq508814
  have eq508958 : False := by grind
  exact eq508958
