import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq89
    | exact resolve eq89 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
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
  have eq154 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  clear eq39
  have eq191 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq206 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq215 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq378 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq386 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq14
    | exact resolve eq14 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq704 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq705 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq704 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq869 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq386
    | exact resolve eq386 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq386
    | exact resolve eq386 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq386
    | exact resolve eq386 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3514 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq705 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq705
    | (have j0 := eq705 (τ X0)
       grind)
    | exact resolve eq705 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3522 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3514 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3514
    | (have j0 := eq3514 X0
       grind)
    | exact resolve eq3514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514
  have eq3528 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3522 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3522
    | (have j0 := eq3522 X0
       grind)
    | exact resolve eq3522 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522
  have eq6077 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq169 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq169
    | (have j0 := eq169 x
       grind)
    | exact resolve eq169 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq6102 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6077
  have eq6106 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6102
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6102
    | exact resolve eq6102 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6102
  have eq6123 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6106
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq6106 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6106
  have eq6128 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6123 eq49
    | exact resolve eq49 eq6123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6123
  have eq6250 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq191 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq191
    | (have j0 := eq191 y
       grind)
    | exact resolve eq191 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq6274 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6250
  have eq6277 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6274
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq6274
    | exact resolve eq6274 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq6274
  have eq6301 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6277
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq6277 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6277
  have eq6315 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6301 eq104
    | exact resolve eq104 eq6301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq6301
  have eq6438 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq206
    | (have j0 := eq206 (M.op x y)
       grind)
    | exact resolve eq206 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq6461 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6438
  have eq6463 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq131 eq6461
    | exact resolve eq6461 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq6461
  have eq6494 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6463
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq6463 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6463
  have eq6517 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6494 eq154
    | exact resolve eq154 eq6494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq6494
  have eq11129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq11130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq11129
    | exact resolve eq11129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11129
  have eq11141 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq11130
       have r₂ := eq27
       grind)
    | exact resolve eq11130 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11130
  have eq11143 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq11141
    | exact resolve eq11141 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11141
  have eq11145 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq11143 eq6315
    | exact resolve eq6315 eq11143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6315 eq11143
  have eq11212 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq11145
    | exact resolve eq11145 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11145
  have eq11213 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3528 y
       grind)
    | (have r₁ := eq11212
       have r₂ := eq3528 y
       grind)
    | exact resolve eq11212 eq3528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528 eq11212
  have eq11215 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq386 y X0
       have i₂ := eq11213
       grind)
    | exact superpose eq11213 eq386
    | exact resolve eq386 eq11213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11217 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq11213
       grind)
    | exact superpose eq11213 eq13
    | (have r₁ := eq13 X0 y
       have r₂ := eq11213
       grind)
    | exact resolve eq13 eq11213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11218 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq11213
       grind)
    | exact superpose eq11213 eq14
    | exact resolve eq14 eq11213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11213
  have eq11251 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq11217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11217
  have eq11266 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11218 X0
       have i₂ := eq869 y X0
       grind)
    | exact superpose eq869 eq11218
    | exact resolve eq11218 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11218
  have eq12020 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq705 y
       have i₂ := eq11251 y
       grind)
    | exact superpose eq11251 eq705
    | (have j0 := eq705 y
       grind)
    | exact resolve eq705 eq11251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq11251
  have eq12035 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12020
  have eq12047 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12035
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12035
    | exact resolve eq12035 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12035
  have eq12222 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq12047 eq386
    | exact resolve eq386 eq12047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq12225 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq12047 eq14
    | exact resolve eq14 eq12047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12047
  have eq12273 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12225 x
       have i₂ := eq869 sF3 x
       grind)
    | exact superpose eq869 eq12225
    | exact resolve eq12225 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq12225
  have eq19320 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11215 X0
       have i₂ := eq11266 X0
       grind)
    | exact superpose eq11266 eq11215
    | exact resolve eq11215 eq11266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11215
  have eq19382 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19320
  have eq19431 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11266 X0
       have i₂ := eq19382 X0
       grind)
    | exact superpose eq19382 eq11266
    | exact resolve eq11266 eq19382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11266 eq19382
  have eq19515 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19431 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19431
  have eq19575 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19515 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19515
    | (have j0 := eq19515 x
       grind)
    | exact resolve eq19515 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19515
  have eq19832 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19575 eq873
    | exact resolve eq873 eq19575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19575
  have eq19861 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19832 eq6128
    | exact resolve eq6128 eq19832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6128 eq19832
  have eq19952 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq19861
    | exact resolve eq19861 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19861
  have eq20115 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq19952
       grind)
    | exact superpose eq19952 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq19952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19952
  have eq20134 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20115
  have eq20347 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq20134
       grind)
    | exact superpose eq20134 eq50
    | exact resolve eq50 eq20134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20348 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq20134
       grind)
    | exact superpose eq20134 eq53
    | exact resolve eq53 eq20134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq20134
  have eq20427 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq871 eq20348
    | exact resolve eq20348 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20348
  have eq29482 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20427 eq20347
    | exact resolve eq20347 eq20427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20347 eq20427
  have eq29532 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq29482
  have eq29534 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29532
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29532
    | exact resolve eq29532 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29532
  have eq29535 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq29534
  have eq29537 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29535 eq20
    | exact resolve eq20 eq29535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29535
  have eq29677 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29537
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29537
    | exact resolve eq29537 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29537
  have eq362654 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq12273 eq12222
    | exact resolve eq12222 eq12273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12222
  have eq362889 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq362654 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362654
  have eq363230 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4⟩ := hcon
    have f363230_15 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f363230_16 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f363230_24 : (σ y) ≠ (M.op X0 (σ y)) := by grind
    have f363230_27 : x ≠ (M.op x y) := by grind
    have f363230_28 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f363230_29 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f363230_16 X0
         grind)
      | (have r₁ := f363230_16 X0
         have r₂ := f363230_27
         grind)
      | exact resolve f363230_16 f363230_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f363230_30 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f363230_15 X0
         grind)
      | (have r₁ := f363230_15 X0
         have r₂ := f363230_27
         grind)
      | exact resolve f363230_15 f363230_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f363230_31 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f363230_29 X0
         grind)
      | (have r₁ := f363230_29 X0
         have r₂ := f363230_28
         grind)
      | exact resolve f363230_29 f363230_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f363230_32 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
      intro X0
      first
      | (have j0 := f363230_30 X0
         grind)
      | (have r₁ := f363230_30 X0
         have r₂ := f363230_28
         grind)
      | exact resolve f363230_30 f363230_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f363230_33 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
      intro X0
      first
      | (have i₁ := f363230_32 X0
         have i₂ := f363230_31 X0
         grind)
      | exact superpose f363230_31 f363230_32
      | exact resolve f363230_32 f363230_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f363230_34 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f363230_24
         have i₂ := f363230_33 X0
         grind)
      | exact superpose f363230_33 f363230_24
      | (have r₁ := f363230_24
         have r₂ := f363230_33 X0
         grind)
      | exact resolve f363230_24 f363230_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f363230_35 : False := by grind
    exact f363230_35
  clear eq12273 eq362889
  have eq363777 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq363230 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363230
  have eq364077 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq363777
    | (have j0 := eq363777 (σ x)
       grind)
    | exact resolve eq363777 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363777
  have eq365854 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq364077 eq27
    | exact resolve eq27 eq364077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364077
  have eq366021 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq365854
       have r₂ := eq29677
       grind)
    | exact resolve eq365854 eq29677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365854
  have eq366028 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq366021 eq215
    | exact resolve eq215 eq366021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq366060 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq366021 eq873
    | exact resolve eq873 eq366021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq366021
  have eq371149 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq366060 eq366028
    | exact resolve eq366028 eq366060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366028 eq366060
  have eq371257 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq371149
  have eq371274 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq371257
    | exact resolve eq371257 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371257
  have eq371471 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq371274 eq27
    | exact resolve eq27 eq371274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371274
  have eq371643 : x = (M.op x y) := by
    first
    | (have r₁ := eq371471
       have r₂ := eq29677
       grind)
    | exact resolve eq371471 eq29677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29677 eq371471
  have eq371646 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq371643 eq20
    | exact resolve eq20 eq371643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq371744 : x = (M.op x x) := by
    first
    | exact superpose eq371643 eq871
    | exact resolve eq871 eq371643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq372100 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq371646
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq371646
    | exact resolve eq371646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371646
  have eq372146 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq372100 eq26
    | exact resolve eq26 eq372100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq372572 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq371744
       grind)
    | exact superpose eq371744 eq50
    | exact resolve eq50 eq371744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq372641 : ∀ X0 : G, x ≠ x ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq371744
       grind)
    | exact superpose eq371744 eq13
    | (have r₁ := eq13 X0 x
       have r₂ := eq371744
       grind)
    | exact resolve eq13 eq371744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372732 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq372641 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372641
  have eq372834 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq371643 eq372572
    | exact resolve eq372572 eq371643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372572
  have eq372904 : y = (M.op x y) := by
    first
    | (have i₁ := eq372834
       have i₂ := eq371744
       grind)
    | exact superpose eq371744 eq372834
    | exact resolve eq372834 eq371744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371744 eq372834
  have eq372924 : y = (M.op x y) := by
    first
    | (have i₁ := eq372904
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq372904
    | exact resolve eq372904 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq372904
  have eq372929 : x = y := by
    first
    | exact superpose eq371643 eq372924
    | exact resolve eq372924 eq371643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372924
  have eq372932 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq372929
       grind)
    | exact superpose eq372929 eq24
    | exact resolve eq24 eq372929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq372929
  have eq373694 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq372932
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq372932
    | exact resolve eq372932 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372932
  have eq373876 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq372100 eq373694
    | exact resolve eq373694 eq372100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373694
  have eq374728 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq373876 eq372146
    | exact resolve eq372146 eq373876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372146 eq373876
  have eq376602 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq374728 eq6517
    | exact resolve eq6517 eq374728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6517 eq374728
  have eq376785 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq371643 eq376602
    | exact resolve eq376602 eq371643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371643 eq376602
  have eq376806 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq376785
       have i₂ := eq372732 x
       grind)
    | exact superpose eq372732 eq376785
    | exact resolve eq376785 eq372732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372732 eq376785
  have eq376907 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq376806 eq15
    | exact resolve eq15 eq376806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376806
  have eq377528 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq376907
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq376907
    | exact resolve eq376907 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq376907
  have eq377796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq372100 eq377528
    | exact resolve eq377528 eq372100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372100 eq377528
  have eq378029 : False := by grind
  exact eq378029

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq74 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
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
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq155 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq192 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq519 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq519 X0
       grind)
    | exact superpose eq519 eq14
    | exact resolve eq14 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq519 X0
       grind)
    | exact superpose eq519 eq14
    | exact resolve eq14 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq603 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq55 X3 X2 X4 X0
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq55
  have eq802 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq93 X0 X0
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq93 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq93 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq805 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq806 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq802 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq810 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq806 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq806 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq806 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq895 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq528
    | exact resolve eq528 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq897 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq528
    | exact resolve eq528 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq899 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq528
    | exact resolve eq528 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq930 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq897 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq897
       grind)
    | exact resolve eq12 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq940 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq930
  have eq943 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq899 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq899
       grind)
    | exact resolve eq12 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq943
  have eq1070 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq940 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq940
       grind)
    | exact resolve eq13 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq1070 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1109 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq953 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (σ x) (σ y))
       have r₂ := eq953
       grind)
    | exact resolve eq13 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq1109 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq3626 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq805 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq805
    | (have j0 := eq805 (τ X0)
       grind)
    | exact resolve eq805 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq3634 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3626 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3626
    | (have j0 := eq3626 X0
       grind)
    | exact resolve eq3626 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3626
  have eq3640 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3634 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3634
    | (have j0 := eq3634 X0
       grind)
    | exact resolve eq3634 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3634
  have eq3654 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq810 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq810
    | (have j0 := eq810 (τ X0) X1
       grind)
    | exact resolve eq810 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3662 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3654 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3654
    | (have j0 := eq3654 X0 X1
       grind)
    | exact resolve eq3654 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3654
  have eq3668 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3662 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3662
    | (have j0 := eq3662 X0 X1
       grind)
    | exact resolve eq3662 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq6550 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq192 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq192
    | (have j0 := eq192 y
       grind)
    | exact resolve eq192 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq6574 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6550
  have eq6577 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6574
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq6574
    | exact resolve eq6574 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6574
  have eq6601 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6577
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq6577 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6577
  have eq6615 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6601 eq87
    | exact resolve eq87 eq6601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq9434 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq603 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq14 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq14 eq603
    | exact resolve eq603 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq9471 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9434 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq9434
    | exact resolve eq9434 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9434
  have eq11963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq11963
    | exact resolve eq11963 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11963
  have eq11975 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq11964
       have r₂ := eq27
       grind)
    | exact resolve eq11964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11964
  have eq11977 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq11975
    | exact resolve eq11975 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11975
  have eq11979 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq11977 eq6615
    | exact resolve eq6615 eq11977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11977
  have eq12046 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq11979
    | exact resolve eq11979 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11979
  have eq12047 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3640 y
       grind)
    | (have r₁ := eq12046
       have r₂ := eq3640 y
       grind)
    | exact resolve eq12046 eq3640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12046
  have eq12049 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq12047
       grind)
    | exact superpose eq12047 eq14
    | exact resolve eq14 eq12047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12081 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq529 y X0
       have i₂ := eq12047
       grind)
    | exact superpose eq12047 eq529
    | exact resolve eq529 eq12047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq12047
  have eq12086 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12081 X0
       have i₂ := eq895 y X0
       grind)
    | exact superpose eq895 eq12081
    | exact resolve eq12081 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12081
  have eq12942 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12049 X0
       have i₂ := eq12086 X0
       grind)
    | exact superpose eq12086 eq12049
    | exact resolve eq12049 eq12086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12049
  have eq13003 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq12942 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12942
  have eq13086 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12086 X0
       have i₂ := eq13003 X0
       grind)
    | exact superpose eq13003 eq12086
    | exact resolve eq12086 eq13003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12086 eq13003
  have eq13177 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq13086 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13086
  have eq13484 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13177 x
       grind)
    | exact superpose eq13177 eq18
    | (have j1 := eq13177 x
       grind)
    | exact resolve eq18 eq13177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13177
  have eq13539 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13484
  have eq13577 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13539 eq953
    | exact resolve eq953 eq13539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq13579 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13539 eq1110
    | exact resolve eq1110 eq13539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq13539
  have eq17803 : (τ (σ y)) = (k y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13577 eq6615
    | exact resolve eq6615 eq13577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6615 eq13577
  have eq17877 : (σ x) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17803
    | exact resolve eq17803 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17803
  have eq19594 : (τ (σ x)) = (k x y) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17877 eq59
    | exact resolve eq59 eq17877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19595 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17877 eq115
    | exact resolve eq115 eq17877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq17877
  have eq19611 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (k y y) := by grind
  clear eq19595
  have eq19623 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq3640 y
       grind)
    | (have r₁ := eq19611
       have r₂ := eq3640 y
       grind)
    | exact resolve eq19611 eq3640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3640 eq19611
  have eq19624 : y = (k y y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq19594
    | exact resolve eq19594 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19594
  have eq19637 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq19623
       grind)
    | exact superpose eq19623 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq19623
       grind)
    | exact resolve eq13 eq19623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19638 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq19623
       grind)
    | exact superpose eq19623 eq14
    | exact resolve eq14 eq19623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19623
  have eq19675 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq19637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19637
  have eq19694 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq19638 X0
       have i₂ := eq895 y X0
       grind)
    | exact superpose eq895 eq19638
    | exact resolve eq19638 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19638
  have eq20769 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq19624
       grind)
    | exact superpose eq19624 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq19624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19624
  have eq20785 : y = (M.op y y) ∨ x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq20769
  have eq20800 : y = (M.op y y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq20785
       have r₂ := eq74
       grind)
    | exact resolve eq20785 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq20785
  have eq20837 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq20800
       grind)
    | exact superpose eq20800 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq20800
       grind)
    | exact resolve eq13 eq20800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20875 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq20837 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20837
  have eq21209 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq20875 y
       grind)
    | exact superpose eq20875 eq72
    | exact resolve eq72 eq20875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq20875
  have eq21288 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (k x y) := by
    first
    | exact superpose eq6601 eq21209
    | exact resolve eq21209 eq6601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6601 eq21209
  have eq24074 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq21288
       have i₂ := eq20800
       grind)
    | exact superpose eq20800 eq21288
    | exact resolve eq21288 eq20800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20800 eq21288
  have eq24131 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by grind
  clear eq24074
  have eq24134 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq24131
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24131
    | exact resolve eq24131 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24131
  have eq24144 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq24134 eq528
    | exact resolve eq528 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24147 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq24134 eq14
    | exact resolve eq14 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24134
  have eq24210 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq24147 x
       have i₂ := eq895 sF3 x
       grind)
    | exact superpose eq895 eq24147
    | exact resolve eq24147 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24147
  have eq29404 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (k x y) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq24210 eq24144
    | exact resolve eq24144 eq24210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24144 eq24210
  have eq29483 : ∀ X0 : G, x = (k x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq29404 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29404
  have eq29557 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq29483 X0
       grind)
    | exact superpose eq29483 eq44
    | (have j1 := eq29483 X0
       grind)
    | exact resolve eq44 eq29483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq29483
  have eq29592 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29557 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29557
    | (have j0 := eq29557 X0
       grind)
    | exact resolve eq29557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29557
  have eq42157 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13579
  have eq42163 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq42157
       have r₂ := eq29592 (σ x)
       grind)
    | exact resolve eq42157 eq29592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42157
  have eq42186 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42163 eq59
    | exact resolve eq59 eq42163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq42163
  have eq42240 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq42186
    | exact resolve eq42186 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42186
  have eq42264 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19675 x
       have i₂ := eq42240
       grind)
    | exact superpose eq42240 eq19675
    | exact resolve eq19675 eq42240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19675 eq42240
  have eq42277 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq42264
  have eq42959 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19694 x
       have i₂ := eq42277
       grind)
    | exact superpose eq42277 eq19694
    | exact resolve eq19694 eq42277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19694 eq42277
  have eq43017 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq42959
  have eq43023 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq43017
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43017
    | exact resolve eq43017 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43017
  have eq43024 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq43023
  have eq43027 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43024 eq28
    | exact resolve eq28 eq43024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq43029 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq43024 eq39
    | exact resolve eq39 eq43024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43038 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43024 eq63
    | exact resolve eq63 eq43024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq43024
  have eq43227 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq155 eq43038
    | exact resolve eq43038 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq43038
  have eq43234 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq43029
    | exact resolve eq43029 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq43029
  have eq43236 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq43027
    | exact resolve eq43027 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq43027
  have eq45700 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq1071 eq43227
    | exact resolve eq43227 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071 eq43227
  have eq52680 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (σ (k X0 x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq43234 eq16
    | exact resolve eq16 eq43234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43234
  have eq52806 : ∀ X0 : G, (k X0 x) = (k X0 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq52680 X0
       have i₂ := eq16 (k X0 x)
       grind)
    | exact superpose eq16 eq52680
    | exact resolve eq52680 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52680
  have eq1026360 : x ≠ (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq45700
  have eq1026532 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq940 eq1026360
    | exact resolve eq1026360 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq1026360
  have eq1026533 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq1026532
  have eq1026534 : x = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1026533
       have r₂ := eq43236
       grind)
    | exact resolve eq1026533 eq43236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43236 eq1026533
  have eq1026939 : x = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1026534 eq52806
    | exact resolve eq52806 eq1026534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52806 eq1026534
  have eq1027025 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq1026939
  have eq1027291 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq810 x X0
       have i₂ := eq1027025
       grind)
    | exact superpose eq1027025 eq810
    | (have j0 := eq810 x X0
       grind)
    | exact resolve eq810 eq1027025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq1027295 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3668 x X0
       have i₂ := eq1027025
       grind)
    | exact superpose eq1027025 eq3668
    | (have j0 := eq3668 x X0
       grind)
    | (have r₁ := eq3668 x x
       have r₂ := eq1027025
       grind)
    | exact resolve eq3668 eq1027025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668 eq1027025
  have eq1027322 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1027295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027295
  have eq1027326 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1027291 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027291
  have eq1027362 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1027326 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1027326
    | (have j0 := eq1027326 X0
       grind)
    | exact resolve eq1027326 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1027326
  have eq1049493 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1027322 y
       grind)
    | exact superpose eq1027322 eq71
    | exact resolve eq71 eq1027322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1027322
  have eq1050732 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1049493
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1049493
    | exact resolve eq1049493 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1049493
  have eq1050839 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1050732
    | exact resolve eq1050732 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050732
  have eq1053865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1027362 eq1050839
    | exact resolve eq1050839 eq1027362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027362 eq1050839
  have eq1054448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1053865
  have eq1054791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1054448
    | exact resolve eq1054448 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054448
  have eq1054863 : y = (M.op x y) := by
    first
    | (have r₁ := eq1054791
       have r₂ := eq27
       grind)
    | exact resolve eq1054791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054791
  have eq1054875 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1054863 eq20
    | exact resolve eq20 eq1054863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1054863
  have eq1055690 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1054875
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1054875
    | exact resolve eq1054875 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1054875
  have eq1055728 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1055690 eq26
    | exact resolve eq26 eq1055690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1055732 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1055690 eq51
    | exact resolve eq51 eq1055690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1056143 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1055690 eq29592
    | exact resolve eq29592 eq1055690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29592 eq1055690
  have eq1076400 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq1056143 (k X0 x)
       grind)
    | exact superpose eq1056143 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       have j1 := eq1056143 (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1056143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056143
  have eq1076418 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1055728 eq1076400
    | (have j0 := eq1076400 (σ (M.op x y))
       grind)
    | exact resolve eq1076400 eq1055728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076400
  have eq1076453 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1055728 eq1076418
    | (have j0 := eq1076418 (σ (M.op x y))
       grind)
    | exact resolve eq1076418 eq1055728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076418
  have eq1076486 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1076453 (σ (M.op x y))
       grind)
    | (have r₁ := eq1076453 X0
       have r₂ := eq27
       grind)
    | exact resolve eq1076453 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076453
  have eq1612891 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j0 := eq1076486 (σ (M.op x y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076486
  have eq1612892 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1612891
  have eq1613258 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1612892 eq528
    | exact resolve eq528 eq1612892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq1613583 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1612892 eq9471
    | exact resolve eq9471 eq1612892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9471 eq1612892
  have eq1613611 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1613583 x
       have i₂ := eq895 sF1 x
       grind)
    | exact superpose eq895 eq1613583
    | exact resolve eq1613583 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq1613583
  have eq1627415 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1613611 eq1613258
    | exact resolve eq1613258 eq1613611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613258
  have eq1628214 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1627415 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627415
  have eq1628952 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1628214 eq1613611
    | exact resolve eq1613611 eq1628214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613611 eq1628214
  have eq1631014 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1628952 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628952
  have eq1638663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1631014 eq1055728
    | exact resolve eq1055728 eq1631014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631014
  have eq1639200 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1638663
       have r₂ := eq27
       grind)
    | exact resolve eq1638663 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638663
  have eq1639911 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1639200 eq899
    | exact resolve eq899 eq1639200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq1641033 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1639911 eq1055732
    | exact resolve eq1055732 eq1639911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055732
  have eq1641577 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1639200 eq1641033
    | exact resolve eq1641033 eq1639200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639200 eq1641033
  have eq1641877 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1639911 eq1641577
    | exact resolve eq1641577 eq1639911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639911 eq1641577
  have eq1642152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1055728 eq1641877
    | exact resolve eq1641877 eq1055728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055728 eq1641877
  have eq1642350 : False := by grind
  exact eq1642350

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq104 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq105 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq106 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq106 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq107 (σ X0)
       grind)
    | exact superpose eq107 eq10
    | exact resolve eq10 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq43
    | exact resolve eq43 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq112 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq107 sF2
       grind)
    | exact superpose eq107 eq49
    | exact resolve eq49 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq113 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq112
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq112
    | exact resolve eq112 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq107 sF2
       grind)
    | exact superpose eq107 eq110
    | exact resolve eq110 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq116 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq109
    | exact resolve eq109 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq109
  have eq457 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq463 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq457 X0
       grind)
    | exact superpose eq457 eq14
    | exact resolve eq14 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq740 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq116 X1
       grind)
    | exact superpose eq116 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq741 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq740 X0 X1
       have i₂ := eq116 X1
       grind)
    | exact superpose eq116 eq740
    | (have j0 := eq740 X0 X1
       grind)
    | exact resolve eq740 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq740
  have eq882 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq741 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq1219 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq463 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq463
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1222 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq463
    | exact resolve eq463 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1225 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq463
    | exact resolve eq463 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq1340 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op x X0)
       have i₂ := eq1219 x X0
       grind)
    | exact superpose eq1219 eq53
    | exact resolve eq53 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1345 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op sF2 x)
       have i₂ := eq1219 sF2 x
       grind)
    | exact superpose eq1219 eq54
    | exact resolve eq54 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1219
  have eq26969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq26969
    | exact resolve eq26969 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26969
  have eq26988 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq26977
       have r₂ := eq27
       grind)
    | exact resolve eq26977 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26977
  have eq26992 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq26988
    | exact resolve eq26988 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26988
  have eq26994 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26992 eq105
    | (have r₁ := eq105
       have r₂ := eq26992
       grind)
    | exact resolve eq105 eq26992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq27073 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq26992
  have eq27075 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq26994
  have eq27809 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq27075
       have r₂ := eq27073
       grind)
    | exact resolve eq27075 eq27073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27073 eq27075
  have eq27815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27809 eq92
    | exact resolve eq92 eq27809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq27809
  have eq27831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq27815
  have eq27834 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq27831
       have r₂ := eq27
       grind)
    | exact resolve eq27831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27831
  have eq27892 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27834 eq113
    | exact resolve eq113 eq27834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27834
  have eq28015 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq27892
    | exact resolve eq27892 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27892
  have eq28016 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq28015
  have eq28030 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq28016
       grind)
    | exact superpose eq28016 eq104
    | (have r₁ := eq104
       have r₂ := eq28016
       grind)
    | exact resolve eq104 eq28016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq28031 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq28016
       grind)
    | exact superpose eq28016 eq115
    | exact resolve eq115 eq28016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28112 : x ≠ (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq28016
  have eq28114 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  clear eq28030
  have eq28133 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq28031
    | exact resolve eq28031 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28031
  have eq29884 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28114
       have r₂ := eq28112
       grind)
    | exact resolve eq28114 eq28112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28112 eq28114
  have eq29902 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq882 x y
       have i₂ := eq29884
       grind)
    | exact superpose eq29884 eq882
    | (have j0 := eq882 x y
       grind)
    | exact resolve eq882 eq29884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq29884
  have eq29905 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29902
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq29902
    | exact resolve eq29902 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29902
  have eq29921 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq29905
    | exact resolve eq29905 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29905
  have eq29930 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29921
       have r₂ := eq28133
       grind)
    | exact resolve eq29921 eq28133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29921
  have eq29937 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29930
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq29930
    | exact resolve eq29930 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29930
  have eq29944 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29937
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29937
    | exact resolve eq29937 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29937
  have eq29951 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29944
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29944
    | exact resolve eq29944 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29944
  have eq29958 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq29951
    | exact resolve eq29951 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29951
  have eq29965 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29958
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq29958
    | exact resolve eq29958 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29958
  have eq29972 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29965
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29965
    | exact resolve eq29965 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29965
  have eq32110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29972 eq28133
    | exact resolve eq28133 eq29972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28133 eq29972
  have eq32197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq32110
  have eq32215 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq32197
       have r₂ := eq27
       grind)
    | exact resolve eq32197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32197
  have eq32965 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq32215 eq113
    | exact resolve eq113 eq32215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq32215
  have eq33116 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq32965
    | exact resolve eq32965 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq32965
  have eq33117 : x = (M.op x x) := by grind
  clear eq33116
  have eq33132 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq33117
       grind)
    | exact superpose eq33117 eq115
    | exact resolve eq115 eq33117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq33141 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq33117
       grind)
    | exact superpose eq33117 eq50
    | exact resolve eq50 eq33117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq33158 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq1340 x
       have i₂ := eq33117
       grind)
    | exact superpose eq33117 eq1340
    | exact resolve eq1340 eq33117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340 eq33117
  have eq33242 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1222 eq33158
    | exact resolve eq33158 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222 eq33158
  have eq33258 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33132
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33132
    | exact resolve eq33132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq33132
  have eq33331 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq33258 eq51
    | exact resolve eq51 eq33258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq33348 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq33258 eq1345
    | exact resolve eq1345 eq33258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345 eq33258
  have eq33435 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1225 eq33348
    | exact resolve eq33348 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq33348
  have eq33499 : y = (M.op x y) := by
    first
    | exact superpose eq33242 eq33141
    | exact resolve eq33141 eq33242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33141 eq33242
  have eq33500 : y = (M.op x y) := by
    first
    | (have i₁ := eq33499
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33499
    | exact resolve eq33499 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq33499
  have eq33501 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq33500 eq20
    | exact resolve eq20 eq33500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq33500
  have eq33673 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq33501
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33501
    | exact resolve eq33501 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq33501
  have eq33695 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq33673 eq26
    | exact resolve eq26 eq33673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq34414 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq33673 eq33331
    | exact resolve eq33331 eq33673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33331 eq33673
  have eq34415 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq33435 eq34414
    | exact resolve eq34414 eq33435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33435 eq34414
  have eq34416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33695 eq34415
    | exact resolve eq34415 eq33695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33695 eq34415
  have eq34417 : False := by grind
  exact eq34417

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq44
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq44 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq106
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq430 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq654 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq108 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq654
    | exact resolve eq654 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq658 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq655
       have r₂ := eq27
       grind)
    | exact resolve eq655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq662 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq658 eq14
    | exact resolve eq14 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq760 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq662 sF3
       have i₂ := eq430 sF3
       grind)
    | exact superpose eq430 eq662
    | exact resolve eq662 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq784 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq760 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq760
       grind)
    | exact resolve eq13 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq785 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq784 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq785 eq108
    | exact resolve eq108 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq785
  have eq921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq916
  have eq925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq921
    | exact resolve eq921 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq927 : y = (M.op y x) := by
    first
    | (have r₁ := eq925
       have r₂ := eq27
       grind)
    | exact resolve eq925 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq943 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq14
    | exact resolve eq14 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq14
    | exact resolve eq14 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : x = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq943 x
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq943
    | exact resolve eq943 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq1001 : y = (M.op y y) := by
    first
    | (have i₁ := eq944 y
       have i₂ := eq430 y
       grind)
    | exact superpose eq430 eq944
    | exact resolve eq944 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq944
  have eq1030 : x = (M.op y x) := by
    first
    | (have i₁ := eq977
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq977
    | exact resolve eq977 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1043 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1001
       grind)
    | exact resolve eq13 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1044 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1043 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1045 : x = y := by
    first
    | (have i₁ := eq1030
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq1030
    | exact resolve eq1030 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1046 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq18
    | exact resolve eq18 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1047 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq24
    | exact resolve eq24 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1062 : x = (M.op x x) := by
    first
    | (have i₁ := eq927
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq927
    | exact resolve eq927 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq1075 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1047
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1047
    | exact resolve eq1047 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1076 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1075 eq26
    | exact resolve eq26 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1075
  have eq1179 : x = (M.op x y) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq1062
    | exact resolve eq1062 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1180 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1179 eq20
    | exact resolve eq20 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1218 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1180
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1180
    | exact resolve eq1180 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1180
  have eq1261 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1218 eq1076
    | exact resolve eq1076 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1296 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1044 X0
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq1044
    | exact resolve eq1044 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq1045
  have eq1300 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1296 x
       grind)
    | exact superpose eq1296 eq43
    | exact resolve eq43 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1296
  have eq1308 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1300
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq1300
    | exact resolve eq1300 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046 eq1300
  have eq1314 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1218 eq1308
    | exact resolve eq1308 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218 eq1308
  have eq1317 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1314
    | exact resolve eq1314 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1314
  have eq1325 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1317 eq74
    | (have j0 := eq74 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq74 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1317
  have eq1326 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1325
  have eq1328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1261 eq1326
    | exact resolve eq1326 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261 eq1326
  have eq1331 : False := by grind
  exact eq1331

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq184 : ∀ X0 : G, y = (M.op (M.op y (M.op (M.op (M.op x y) (M.op x y)) X0)) y) := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq191 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq622 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq685 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq786 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq620
       grind)
    | exact superpose eq620 eq39
    | exact resolve eq39 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq787 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq786
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq786
    | exact resolve eq786 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq789 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq787
    | exact resolve eq787 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq851 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq191
    | exact resolve eq191 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq866 : y = (M.op (M.op y (M.op x y)) y) := by
    first
    | (have i₁ := eq184 sF0
       have i₂ := eq851 sF0
       grind)
    | exact superpose eq851 eq184
    | exact resolve eq184 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq874 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq851 X0
       grind)
    | exact superpose eq851 eq16
    | exact resolve eq16 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq851 X0
       grind)
    | exact superpose eq851 eq16
    | exact resolve eq16 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq922 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq874 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq874
    | exact resolve eq874 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq926 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq874
    | exact resolve eq874 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq930 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq874
    | exact resolve eq874 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq789 eq622
    | exact resolve eq622 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq789
  have eq1624 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1617
       have r₂ := eq27
       grind)
    | exact resolve eq1617 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq1647 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1624 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1624
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1624
       grind)
    | exact resolve eq13 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1648 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1647 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1789 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1648 eq1624
    | exact resolve eq1624 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624 eq1648
  have eq1800 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq1789
  have eq1874 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1800 eq141
    | exact resolve eq141 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1800
  have eq1881 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq1874
    | exact resolve eq1874 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq1884 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq686 x
       grind)
    | (have r₁ := eq1881
       have r₂ := eq686 x
       grind)
    | exact resolve eq1881 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq1881
  have eq1898 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1884
       grind)
    | exact superpose eq1884 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1884
       grind)
    | exact resolve eq13 eq1884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1907 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq1967 : ∀ X0 : G, (M.op (M.op (M.op (k x x) X0) x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq874 x X0
       have i₂ := eq1907 x
       grind)
    | exact superpose eq1907 eq874
    | exact resolve eq874 eq1907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq1983 : ∀ X0 : G, x = (k (M.op x (M.op (M.op x x) X0)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq875 x X0
       have i₂ := eq1907 (M.op x (M.op (M.op x x) X0))
       grind)
    | exact superpose eq1907 eq875
    | exact resolve eq875 eq1907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq2036 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1884
       have i₂ := eq1907 x
       grind)
    | exact superpose eq1907 eq1884
    | exact resolve eq1884 eq1907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2055 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2036
  have eq2082 : ∀ X0 : G, x = (k (M.op x (M.op x X0)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1884 eq1983
    | exact resolve eq1983 eq1884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884 eq1983
  have eq2088 : ∀ X0 : G, (M.op (k (M.op (k x x) X0) x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1907 eq1967
    | exact resolve eq1967 eq1907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907 eq1967
  have eq2115 : ∀ X0 : G, x = (k (M.op x X0) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2082 X0
       have i₂ := eq922 x X0
       grind)
    | exact superpose eq922 eq2082
    | exact resolve eq2082 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq2082
  have eq2116 : ∀ X0 : G, (M.op (k (M.op x X0) x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2055 eq2088
    | exact resolve eq2088 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq2120 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2115 eq2116
    | exact resolve eq2116 eq2115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115 eq2116
  have eq2131 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq2055
       grind)
    | exact superpose eq2055 eq39
    | exact resolve eq39 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq2138 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2131
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2131
    | exact resolve eq2131 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq2151 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2120 y
       grind)
    | exact superpose eq2120 eq18
    | (have j1 := eq2120 y
       grind)
    | exact resolve eq18 eq2120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2159 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 x X0
       have i₂ := eq2120 X0
       grind)
    | exact superpose eq2120 eq16
    | exact resolve eq16 eq2120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2187 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq2120 eq2159
    | exact resolve eq2159 eq2120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120 eq2159
  have eq2342 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2151 eq185
    | exact resolve eq185 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2357 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2151 eq930
    | exact resolve eq930 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2372 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2357 eq2342
    | exact resolve eq2342 eq2357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342 eq2357
  have eq2376 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2372
    | exact resolve eq2372 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372
  have eq2377 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2151 eq2376
    | exact resolve eq2376 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2376
  have eq2379 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2377 eq31
    | exact resolve eq31 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2377
  have eq2428 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2379
    | exact resolve eq2379 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2379
  have eq2434 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq2428
       grind)
    | exact superpose eq2428 eq24
    | exact resolve eq24 eq2428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428
  have eq2460 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq2434
    | exact resolve eq2434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2434
  have eq2617 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2138 eq684
    | (have j0 := eq684 (σ x) (σ x)
       grind)
    | (have r₁ := eq684 (σ x) (σ x)
       have r₂ := eq2138
       grind)
    | exact resolve eq684 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq2138
  have eq2618 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2617
  have eq2619 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2618
  have eq2673 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2619 eq16
    | exact resolve eq16 eq2619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq2685 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2187 eq2673
    | exact resolve eq2673 eq2187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187 eq2673
  have eq2700 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2685 eq26
    | (have j1 := eq2685 (σ y)
       grind)
    | exact resolve eq26 eq2685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq2739 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2700 eq27
    | exact resolve eq27 eq2700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700
  have eq2770 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2460 eq2739
    | (have r₁ := eq2739
       have r₂ := eq2460
       grind)
    | exact resolve eq2739 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739
  have eq2771 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2770
  have eq2772 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2771
  have eq2773 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2151 eq2772
    | exact resolve eq2772 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151 eq2772
  have eq2774 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2773
  have eq2776 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2774 eq27
    | exact resolve eq27 eq2774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2779 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2774 eq185
    | exact resolve eq185 eq2774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq2794 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2774 eq930
    | exact resolve eq930 eq2774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq2810 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2794 eq2779
    | exact resolve eq2779 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2779
  have eq2814 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2810
    | exact resolve eq2810 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810
  have eq2815 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2774 eq2814
    | exact resolve eq2814 eq2774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774 eq2814
  have eq2816 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2460 eq2776
    | exact resolve eq2776 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460
  have eq2817 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2816
  have eq2818 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2817
       have r₂ := eq2815
       grind)
    | exact resolve eq2817 eq2815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815 eq2817
  have eq2874 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq2818
       grind)
    | exact superpose eq2818 eq18
    | exact resolve eq18 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2885 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq926
       have i₂ := eq2818
       grind)
    | exact superpose eq2818 eq926
    | exact resolve eq926 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2944 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2794 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq2794
       grind)
    | exact resolve eq13 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2953 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2944 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944
  have eq2982 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq2885 eq180
    | exact resolve eq180 eq2885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq2885
  have eq2998 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2874 eq2982
    | exact resolve eq2982 eq2874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874 eq2982
  have eq3026 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq2998
  have eq3027 : x = y := by
    first
    | (have r₁ := eq3026
       have r₂ := eq2818
       grind)
    | exact resolve eq3026 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818 eq3026
  have eq3033 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3027
       grind)
    | exact superpose eq3027 eq18
    | exact resolve eq18 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3034 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3027
       grind)
    | exact superpose eq3027 eq24
    | exact resolve eq24 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3050 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq866
       have i₂ := eq3027
       grind)
    | exact superpose eq3027 eq866
    | exact resolve eq866 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq3027
  have eq3059 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq926 eq3050
    | exact resolve eq3050 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926 eq3050
  have eq3062 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3034
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3034
    | exact resolve eq3034 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3034
  have eq3063 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3062 eq26
    | exact resolve eq26 eq3062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3062
  have eq3126 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq3033
       grind)
    | exact superpose eq3033 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3033
  have eq3138 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq3126
  have eq3188 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3063 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq3063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063
  have eq3200 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3188
  have eq4203 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3138
       grind)
    | exact superpose eq3138 eq39
    | exact resolve eq39 eq3138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3138
  have eq4215 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4203
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4203
    | exact resolve eq4203 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4203
  have eq4217 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4215
    | exact resolve eq4215 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4215
  have eq4936 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2953 eq2794
    | exact resolve eq2794 eq2953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794 eq2953
  have eq4966 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4936
  have eq5172 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4966 eq4217
    | exact resolve eq4217 eq4966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217 eq4966
  have eq5191 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq5172
  have eq5197 : x = (M.op x y) := by
    first
    | (have r₁ := eq5191
       have r₂ := eq2776
       grind)
    | exact resolve eq5191 eq2776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2776 eq5191
  have eq5206 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq22
    | exact resolve eq22 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq5226 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3059
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq3059
    | exact resolve eq3059 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3059 eq5197
  have eq5242 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5206 eq20
    | exact resolve eq20 eq5206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5206
  have eq5324 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5226 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq5226
       grind)
    | exact resolve eq13 eq5226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5337 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq5324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5324
  have eq6092 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5337 eq5226
    | exact resolve eq5226 eq5337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5226 eq5337
  have eq6373 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6092 eq37
    | exact resolve eq37 eq6092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq6092
  have eq6389 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq6373
    | exact resolve eq6373 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6373
  have eq6391 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5242 eq6389
    | exact resolve eq6389 eq5242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6389
  have eq6498 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6391 eq3200
    | exact resolve eq3200 eq6391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3200 eq6391
  have eq6515 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6498
  have eq6525 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq6515 eq27
    | exact resolve eq27 eq6515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6515
  have eq6561 : False := by grind
  exact eq6561

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq24
  have eq64 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4)) X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq19 X0 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4 X5
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4) X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X4 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq67 (M.op X0 X1)
       grind)
    | exact superpose eq67 eq19
    | exact resolve eq19 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq19
    | exact resolve eq19 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq403 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq288 x y
       grind)
    | exact superpose eq288 eq16
    | (have j1 := eq288 x y
       grind)
    | exact resolve eq16 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq288 X0 X1
       grind)
    | exact superpose eq288 eq9
    | (have j1 := eq288 X0 X1
       grind)
    | exact resolve eq9 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq288 X0 X0
       grind)
    | exact superpose eq288 eq67
    | (have j1 := eq288 X0 X0
       grind)
    | exact resolve eq67 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq288
  have eq425 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq479 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1095 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq425 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq425
    | exact resolve eq425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq1126 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1095 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1095
    | (have j0 := eq1095 X0
       grind)
    | exact resolve eq1095 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1095
  have eq1130 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1126 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1126
    | (have j0 := eq1126 X0
       grind)
    | exact resolve eq1126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1227 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1130 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq1130
    | (have j0 := eq1130 (τ X0)
       grind)
    | exact resolve eq1130 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2542 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X5)) X6)) X1) X0) X7)) X8) X1) X8) = X8 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq68 X1 (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X5)) X6)) X0 X7 X8
       have i₂ := eq64 X0 X2 X3 X4 X5 X6
       grind)
    | exact superpose eq64 eq68
    | exact resolve eq68 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq68
  have eq6556 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq403
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq403
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq403 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq6559 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq6556
  have eq7259 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq404 (τ X0) (τ X1) X2
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq404
    | (have j0 := eq404 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq404 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq404
  have eq7391 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7259 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7259
    | (have j0 := eq7259 X0 X1 X2
       grind)
    | exact resolve eq7259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7259
  have eq7402 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7391 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7391
    | (have j0 := eq7391 X0 X1 X2
       grind)
    | exact resolve eq7391 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7391
  have eq7412 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7402 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7402
    | (have j0 := eq7402 X0 X1 X2
       grind)
    | exact resolve eq7402 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7402
  have eq7421 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7412 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7412
    | (have j0 := eq7412 X0 X1 X2
       grind)
    | exact resolve eq7412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7412
  have eq7430 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7421 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7421
    | (have j0 := eq7421 (σ (τ X1)) X1 X2
       grind)
    | exact resolve eq7421 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7421
  have eq7435 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7430 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7430
    | (have j0 := eq7430 X0 X1 X2
       grind)
    | exact resolve eq7430 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7430
  have eq16612 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op (k X1 X0) X0) (k X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83 (k X1 X0) X1 X0
       have i₂ := eq7435 X1 X0 (k X1 X0)
       grind)
    | exact superpose eq7435 eq83
    | (have j1 := eq7435 X1 X0 x
       grind)
    | exact resolve eq83 eq7435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq7435
  have eq45709 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq6559
       grind)
    | exact superpose eq6559 eq12
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq6559
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq6559
       grind)
    | exact resolve eq12 eq6559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6559
  have eq45850 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq45709 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45709
  have eq50655 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16612 X0 X0
       have i₂ := eq1130 X0
       grind)
    | exact superpose eq1130 eq16612
    | (have j0 := eq16612 X0 X0
       have j1 := eq1130 X0
       grind)
    | exact resolve eq16612 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq16612
  have eq50843 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq50655 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50655
  have eq50865 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50843 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq50843
    | (have j0 := eq50843 (σ X0)
       grind)
    | exact resolve eq50843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50843
  have eq323592 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq86 (σ y) (σ x)
       have i₂ := eq45850 X0
       grind)
    | exact superpose eq45850 eq86
    | (have j1 := eq45850 X0
       grind)
    | exact resolve eq86 eq45850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45850
  have eq334247 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (k X1 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq323592 X0
       grind)
    | exact superpose eq323592 eq12
    | (have j1 := eq323592 X0
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq323592 X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq323592 X0
       grind)
    | exact resolve eq12 eq323592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323592
  have eq334536 : ∀ X0 X1 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (k X1 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq334247 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334247
  have eq334537 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq334536 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334536
  have eq334750 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1227 (σ y)
       have i₂ := eq334537 (σ y)
       grind)
    | exact superpose eq334537 eq1227
    | (have j0 := eq1227 (σ y)
       grind)
    | exact resolve eq1227 eq334537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq334537
  have eq335230 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq334750
  have eq335394 : y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq335230
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq335230
    | exact resolve eq335230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335230
  have eq335395 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq335394
  have eq335533 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq335395
       grind)
    | exact superpose eq335395 eq73
    | exact resolve eq73 eq335395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335627 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq479 y y x
       have i₂ := eq335395
       grind)
    | exact superpose eq335395 eq479
    | exact resolve eq479 eq335395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335395
  have eq335887 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq335627 X0
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq335627
    | exact resolve eq335627 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335627
  have eq342674 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq335533 X0
       have i₂ := eq335887 X0
       grind)
    | exact superpose eq335887 eq335533
    | exact resolve eq335533 eq335887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335533 eq335887
  have eq343170 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq342674 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342674
  have eq343225 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq86 y x
       have i₂ := eq343170 X0
       grind)
    | exact superpose eq343170 eq86
    | (have j1 := eq343170 y
       grind)
    | exact resolve eq86 eq343170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343170
  have eq343602 : y = (M.op y y) := by
    first
    | (have j0 := eq343225 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343225
  have eq343725 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq343602
       grind)
    | exact superpose eq343602 eq12
    | (have r₁ := eq12 X0 y
       have r₂ := eq343602
       grind)
    | exact resolve eq12 eq343602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343729 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq343602
       grind)
    | exact superpose eq343602 eq73
    | exact resolve eq73 eq343602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq343823 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq479 y y x
       have i₂ := eq343602
       grind)
    | exact superpose eq343602 eq479
    | exact resolve eq479 eq343602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344015 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq343725 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343725
  have eq344086 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq343823 X0
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq343823
    | exact resolve eq343823 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq343823
  have eq344244 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq50865 y
       have i₂ := eq344015 y
       grind)
    | exact superpose eq344015 eq50865
    | (have j0 := eq50865 y
       grind)
    | exact resolve eq50865 eq344015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50865 eq344015
  have eq344667 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq344244
  have eq356480 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq343729 X0
       have i₂ := eq344086 X0
       grind)
    | exact superpose eq344086 eq343729
    | exact resolve eq343729 eq344086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343729
  have eq356482 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq344086 X0
       have i₂ := eq356480 X0
       grind)
    | exact superpose eq356480 eq344086
    | exact resolve eq344086 eq356480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344086
  have eq356586 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq479 y X1 X0
       have i₂ := eq356480 X0
       grind)
    | exact superpose eq356480 eq479
    | exact resolve eq479 eq356480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq357575 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq356586 X0 X0
       have i₂ := eq356480 X0
       grind)
    | exact superpose eq356480 eq356586
    | exact resolve eq356586 eq356480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356586
  have eq364457 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op (M.op y (M.op (M.op y (M.op (M.op y (M.op (M.op y (M.op y X1)) X2)) X3)) X4)) X0) y) X5)) X6) X0) X6) = X6 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2542 y X0 y X1 X2 X3 X4 X5 X6
       have i₂ := eq343602
       grind)
    | exact superpose eq343602 eq2542
    | exact resolve eq2542 eq343602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542 eq343602
  have eq365426 : ∀ X0 X5 X6 : G, (M.op (M.op (M.op (M.op X0 (M.op y X5)) X6) X0) X6) = X6 := by
    intro X0 X5 X6
    first
    | (have i₁ := eq364457 X0 x x x x X5 X6
       have i₂ := eq356482 (M.op (M.op y (M.op (M.op y (M.op (M.op y (M.op (M.op y (M.op y x)) x)) x)) x)) X0)
       grind)
    | exact superpose eq356482 eq364457
    | exact resolve eq364457 eq356482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364457
  have eq365454 : ∀ X0 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X5) X6) X0) X6) = X6 := by
    intro X0 X5 X6
    first
    | (have i₁ := eq365426 X0 X5 X6
       have i₂ := eq356480 X5
       grind)
    | exact superpose eq356480 eq365426
    | exact resolve eq365426 eq356480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356480 eq365426
  have eq391155 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq365454 (σ y) (σ y) X0
       have i₂ := eq344667
       grind)
    | exact superpose eq344667 eq365454
    | exact resolve eq365454 eq344667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344667 eq365454
  have eq392519 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq391155 X0
       have i₂ := eq357575 X0 (σ y)
       grind)
    | exact superpose eq357575 eq391155
    | exact resolve eq391155 eq357575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391155
  have eq394191 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq357575 X0 (σ y)
       have i₂ := eq392519 X0
       grind)
    | exact superpose eq392519 eq357575
    | exact resolve eq357575 eq392519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357575 eq392519
  have eq399076 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq394191 (σ x)
       grind)
    | exact superpose eq394191 eq16
    | exact resolve eq16 eq394191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394191
  have eq399266 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq399076
       have i₂ := eq356482 x
       grind)
    | exact superpose eq356482 eq399076
    | exact resolve eq399076 eq356482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356482 eq399076
  have eq399267 : False := by grind
  exact eq399267

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq19
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq22
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq67 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq31
    | exact resolve eq31 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq130 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq67
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq130 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq130
    | exact resolve eq130 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq508 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq229 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq229
    | exact resolve eq229 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq821 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq508 X1 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq508
    | exact resolve eq508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq1274 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq18 y x
       grind)
    | exact superpose eq18 eq9
    | (have j1 := eq18 y x
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1275 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq16
    | (have j1 := eq18 X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1276 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X1 X2)) X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq16
    | (have j1 := eq18 X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1280 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq18 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1281 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1274
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1274
    | exact resolve eq1274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1282 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1281
       have i₂ := eq18 (σ y) (σ x)
       grind)
    | exact superpose eq18 eq1281
    | (have j1 := eq18 y x
       grind)
    | (have r₁ := eq1281
       have r₂ := eq18 (σ y) (σ x)
       grind)
    | exact resolve eq1281 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1283 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1282
  have eq1284 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1283
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq1283
    | (have j1 := eq18 (σ y) (σ x)
       grind)
    | exact resolve eq1283 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1285 : y = (k x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18 x x
       have i₂ := eq1283
       grind)
    | exact superpose eq1283 eq18
    | (have j0 := eq18 (σ y) (σ x)
       grind)
    | exact resolve eq18 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : ∀ X0 : G, x ≠ y ∨ (M.op x X0) = (k X0 x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1283
       grind)
    | exact superpose eq1283 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1290 : x = y ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq1285
       grind)
    | exact superpose eq1285 eq10
    | exact resolve eq10 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1302 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq1284
       grind)
    | exact superpose eq1284 eq10
    | exact resolve eq10 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1305 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1290
       grind)
    | exact superpose eq1290 eq9
    | exact resolve eq9 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1307 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1302 eq1305
    | exact resolve eq1305 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302 eq1305
  have eq1917 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq1920 : (k y x) = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  have eq1923 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (k (M.op X0 X0) X0)) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq1926 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X1) (k (k X0 X0) X0)) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq18 eq1923
    | (have j0 := eq1923 X0 X1
       have j1 := eq18 X0 X0
       grind)
    | exact resolve eq1923 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq1929 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1917 X0
       have j1 := eq1280 X0
       grind)
    | (have r₁ := eq1917 X0
       have r₂ := eq1280 X0
       grind)
    | exact resolve eq1917 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq2999 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0 x x X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3053 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2999 x
       have i₂ := eq1283
       grind)
    | exact superpose eq1283 eq2999
    | exact resolve eq2999 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3056 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq3057 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq2999 (M.op X0 X1)
       grind)
    | exact superpose eq2999 eq175
    | exact resolve eq175 eq2999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3063 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq18 eq3056
    | (have j0 := eq3056 X0
       have j1 := eq18 X0 X0
       grind)
    | exact resolve eq3056 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3056
  have eq3069 : x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1920
       have i₂ := eq3053
       grind)
    | exact superpose eq3053 eq1920
    | exact resolve eq1920 eq3053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq3079 : x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq3069
  have eq3091 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq10
    | exact resolve eq10 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3079
  have eq3117 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op y (M.op x X0)) X1) x) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x x X0 X1
       have i₂ := eq1283
       grind)
    | exact superpose eq1283 eq176
    | exact resolve eq176 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3133 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (k X0 X0) X1) (k (k X0 X0) X0)) X2) X1) X2) = X2 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 (k X0 X0) X0 X2
       have i₂ := eq1929 X0
       grind)
    | exact superpose eq1929 eq176
    | (have j1 := eq1929 X0
       grind)
    | exact resolve eq176 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq3177 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (k X0 X0) X1) X0) X2) X1) X2) = X2 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq3063 eq3133
    | (have j0 := eq3133 X0 X1 X2
       have j1 := eq3063 X0
       grind)
    | exact resolve eq3133 eq3063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133
  have eq3351 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq2999 X0
       grind)
    | exact superpose eq2999 eq3057
    | (have j1 := eq2999 X0
       grind)
    | exact resolve eq3057 eq2999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999
  have eq3353 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 (M.op (M.op (M.op x X0) (M.op x x)) x)) X0
       have i₂ := eq175 X0 x x x
       grind)
    | exact superpose eq175 eq3057
    | exact resolve eq3057 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3465 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16 (σ x) (σ x) X0
       have i₂ := eq3091
       grind)
    | exact superpose eq3091 eq16
    | exact resolve eq16 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3474 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by grind
  have eq3479 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3351 (σ x)
       have i₂ := eq3091
       grind)
    | exact superpose eq3091 eq3351
    | exact resolve eq3351 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091 eq3351
  have eq3480 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3479 eq3474
    | exact resolve eq3474 eq3479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474
  have eq3481 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3480
  have eq3504 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq3353 X0
       grind)
    | exact superpose eq3353 eq3057
    | (have j1 := eq3353 X0
       grind)
    | exact resolve eq3057 eq3353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353
  have eq3660 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq18 (σ x) (σ y)
       have i₂ := eq3479
       grind)
    | exact superpose eq3479 eq18
    | (have j0 := eq18 (σ x) (σ y)
       grind)
    | exact resolve eq18 eq3479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3670 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3481 eq3660
    | exact resolve eq3660 eq3481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3660
  have eq3674 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3481 eq3670
    | exact resolve eq3670 eq3481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3481 eq3670
  have eq3751 : ∀ X0 X1 : G, (k X1 (M.op (k X0 X0) X0)) = (M.op X0 (k X1 (M.op (k X0 X0) X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3177 X0 X0 (k X1 (M.op (k X0 X0) X0))
       have i₂ := eq1275 X1 (M.op (k X0 X0) X0) X0
       grind)
    | exact superpose eq1275 eq3177
    | (have j0 := eq3177 X0 X1 x
       have j1 := eq1275 X0 X0 x
       grind)
    | exact resolve eq3177 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275 eq3177
  have eq3763 : ∀ X0 X1 : G, (k X1 (k (k X0 X0) X0)) = (M.op X0 (k X1 (k (k X0 X0) X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1929 eq3751
    | (have j0 := eq3751 X0 X1
       have j1 := eq1929 X0
       grind)
    | exact resolve eq3751 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3751
  have eq3777 : ∀ X0 X1 : G, (k X1 (k (k X0 X0) X0)) = (M.op X0 (k X1 (k (k X0 X0) X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op (k (k X0 X0) X0) (k (k X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1929 eq3763
    | (have j0 := eq3763 X0 X1
       have j1 := eq1929 X0
       grind)
    | exact resolve eq3763 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3763
  have eq3788 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (k (k X0 X0) X0) (k (k X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq3063 eq3777
    | (have j0 := eq3777 X0 X1
       have j1 := eq3063 X0
       grind)
    | exact resolve eq3777 eq3063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq3793 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq3063 eq3788
    | (have j0 := eq3788 X0 X1
       have j1 := eq3063 X0
       grind)
    | exact resolve eq3788 eq3063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063 eq3788
  have eq3796 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq18 eq3793
    | (have j0 := eq3793 X0 X1
       have j1 := eq18 X0 X0
       grind)
    | exact resolve eq3793 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3793
  have eq3959 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq3504 X0
       grind)
    | exact superpose eq3504 eq3057
    | (have j1 := eq3504 X0
       grind)
    | exact resolve eq3057 eq3504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504
  have eq4246 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq3959 X0
       grind)
    | exact superpose eq3959 eq3057
    | (have j1 := eq3959 X0
       grind)
    | exact resolve eq3057 eq3959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3959
  have eq4796 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq4246 X0
       grind)
    | exact superpose eq4246 eq3057
    | (have j1 := eq4246 X0
       grind)
    | exact resolve eq3057 eq4246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4246
  have eq4957 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3117 y y
       have i₂ := eq3057 x y
       grind)
    | exact superpose eq3057 eq3117
    | exact resolve eq3117 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3117
  have eq4982 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3053 eq4957
    | exact resolve eq4957 eq3053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3053 eq4957
  have eq4999 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq4982
       grind)
    | exact superpose eq4982 eq9
    | exact resolve eq9 eq4982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4982
  have eq5184 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq4796 X0
       grind)
    | exact superpose eq4796 eq3057
    | (have j1 := eq4796 X0
       grind)
    | exact resolve eq3057 eq4796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4796
  have eq5799 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq5184 X0
       grind)
    | exact superpose eq5184 eq3057
    | (have j1 := eq5184 X0
       grind)
    | exact resolve eq3057 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5184
  have eq6290 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq5799 X0
       grind)
    | exact superpose eq5799 eq3057
    | (have j1 := eq5799 X0
       grind)
    | exact resolve eq3057 eq5799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5799
  have eq6882 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq6290 X0
       grind)
    | exact superpose eq6290 eq3057
    | (have j1 := eq6290 X0
       grind)
    | exact resolve eq3057 eq6290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6290
  have eq7516 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq6882 X0
       grind)
    | exact superpose eq6882 eq3057
    | (have j1 := eq6882 X0
       grind)
    | exact resolve eq3057 eq6882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6882
  have eq8472 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq7516 X0
       grind)
    | exact superpose eq7516 eq3057
    | (have j1 := eq7516 X0
       grind)
    | exact resolve eq3057 eq7516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7516
  have eq8988 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq8472 X0
       grind)
    | exact superpose eq8472 eq3057
    | (have j1 := eq8472 X0
       grind)
    | exact resolve eq3057 eq8472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8472
  have eq9757 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq8988 X0
       grind)
    | exact superpose eq8988 eq3057
    | (have j1 := eq8988 X0
       grind)
    | exact resolve eq3057 eq8988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8988
  have eq10693 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq9757 X0
       grind)
    | exact superpose eq9757 eq3057
    | (have j1 := eq9757 X0
       grind)
    | exact resolve eq3057 eq9757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9757
  have eq11962 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq10693 X0
       grind)
    | exact superpose eq10693 eq3057
    | (have j1 := eq10693 X0
       grind)
    | exact resolve eq3057 eq10693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10693
  have eq12775 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq11962 X0
       grind)
    | exact superpose eq11962 eq3057
    | (have j1 := eq11962 X0
       grind)
    | exact resolve eq3057 eq11962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11962
  have eq13480 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq12775 X0
       grind)
    | exact superpose eq12775 eq3057
    | (have j1 := eq12775 X0
       grind)
    | exact resolve eq3057 eq12775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12775
  have eq14121 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq13480 X0
       grind)
    | exact superpose eq13480 eq3057
    | (have j1 := eq13480 X0
       grind)
    | exact resolve eq3057 eq13480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13480
  have eq14779 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq14121 X0
       grind)
    | exact superpose eq14121 eq3057
    | (have j1 := eq14121 X0
       grind)
    | exact resolve eq3057 eq14121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14121
  have eq15393 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1307
       have i₂ := eq1280 (σ x)
       grind)
    | exact superpose eq1280 eq1307
    | (have j1 := eq1280 (σ x)
       grind)
    | (have r₁ := eq1307
       have r₂ := eq1280 (σ x)
       grind)
    | exact resolve eq1307 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq15396 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq15393
  have eq15485 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq14779 X0
       grind)
    | exact superpose eq14779 eq3057
    | (have j1 := eq14779 X0
       grind)
    | exact resolve eq3057 eq14779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14779
  have eq16093 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq15485 X0
       grind)
    | exact superpose eq15485 eq3057
    | (have j1 := eq15485 X0
       grind)
    | exact resolve eq3057 eq15485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15485
  have eq16697 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq16093 X0
       grind)
    | exact superpose eq16093 eq3057
    | (have j1 := eq16093 X0
       grind)
    | exact resolve eq3057 eq16093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16093
  have eq17063 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3465 (σ x)
       have i₂ := eq1280 (σ x)
       grind)
    | exact superpose eq1280 eq3465
    | (have j1 := eq1280 (σ x)
       grind)
    | exact resolve eq3465 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3465
  have eq17123 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq3479 eq17063
    | exact resolve eq17063 eq3479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479 eq17063
  have eq17136 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq17123
       have r₂ := eq3674
       grind)
    | exact resolve eq17123 eq3674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674 eq17123
  have eq17221 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3796 (σ x) (σ y)
       have i₂ := eq17136
       grind)
    | exact superpose eq17136 eq3796
    | (have j0 := eq3796 (σ x) (σ y)
       grind)
    | exact resolve eq3796 eq17136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17226 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq17221
  have eq17317 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq16697 X0
       grind)
    | exact superpose eq16697 eq3057
    | (have j1 := eq16697 X0
       grind)
    | exact resolve eq3057 eq16697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16697
  have eq17467 : (k x x) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq19 x x
       have i₂ := eq17226
       grind)
    | exact superpose eq17226 eq19
    | exact resolve eq19 eq17226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17504 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (k (σ y) (σ x))) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1926 (σ x) x
       have i₂ := eq17226
       grind)
    | exact superpose eq17226 eq1926
    | (have j0 := eq1926 (σ x) x
       grind)
    | exact resolve eq1926 eq17226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq17505 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1929 (σ x)
       have i₂ := eq17226
       grind)
    | exact superpose eq17226 eq1929
    | (have j0 := eq1929 (σ x)
       grind)
    | exact resolve eq1929 eq17226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17514 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq3796 (σ x) (σ x)
       have i₂ := eq17226
       grind)
    | exact superpose eq17226 eq3796
    | (have j0 := eq3796 (σ x) x
       grind)
    | exact resolve eq3796 eq17226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17521 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17514
  have eq17530 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq17505
  have eq17531 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (k (σ y) (σ x))) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq17504 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17504
  have eq17536 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq17136 eq17530
    | exact resolve eq17530 eq17136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17530
  have eq17537 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17136 eq17531
    | exact resolve eq17531 eq17136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17136 eq17531
  have eq17575 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq17467
       have i₂ := eq15 y
       grind)
    | exact superpose eq15 eq17467
    | exact resolve eq17467 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17467
  have eq17693 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq3796 x x
       have i₂ := eq17575
       grind)
    | exact superpose eq17575 eq3796
    | (have j0 := eq3796 x x
       grind)
    | exact resolve eq3796 eq17575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3796 eq17575
  have eq17698 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq17693
  have eq18145 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq17698
       grind)
    | exact superpose eq17698 eq9
    | exact resolve eq9 eq17698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17698
  have eq18242 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 (M.op X0 X0) X0
       have i₂ := eq17317 X0
       grind)
    | exact superpose eq17317 eq3057
    | (have j1 := eq17317 X0
       grind)
    | exact resolve eq3057 eq17317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057 eq17317
  have eq18724 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq17537 (σ y)
       have i₂ := eq1280 (σ y)
       grind)
    | exact superpose eq1280 eq17537
    | (have j1 := eq1280 (σ x)
       grind)
    | exact resolve eq17537 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17537
  have eq18760 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) ≠ (k (σ y) (σ y)) := by
    first
    | exact superpose eq17536 eq18724
    | exact resolve eq18724 eq17536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17536 eq18724
  have eq18762 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq17521 eq18760
    | exact resolve eq18760 eq17521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18760
  have eq18764 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) ≠ (σ y) := by
    first
    | exact superpose eq17226 eq18762
    | exact resolve eq18762 eq17226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18762
  have eq18765 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq18764
       have r₂ := eq17521
       grind)
    | exact resolve eq18764 eq17521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17521 eq18764
  have eq18824 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq4999
       have i₂ := eq18765
       grind)
    | exact superpose eq18765 eq4999
    | (have r₁ := eq4999
       have r₂ := eq18765
       grind)
    | exact resolve eq4999 eq18765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4999
  have eq18856 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq18824
  have eq18919 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq18856
       grind)
    | exact superpose eq18856 eq9
    | exact resolve eq9 eq18856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18921 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1288 X0
       have i₂ := eq18856
       grind)
    | exact superpose eq18856 eq1288
    | (have j0 := eq1288 X0
       grind)
    | (have r₁ := eq1288 X0
       have r₂ := eq18856
       grind)
    | exact resolve eq1288 eq18856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq18856
  have eq19094 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq18921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18921
  have eq19095 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq19094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19094
  have eq19166 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19095 eq18919
    | exact resolve eq18919 eq19095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18919 eq19095
  have eq19227 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19166
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq19166
    | exact resolve eq19166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19166
  have eq19266 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq18 (σ y) (σ x)
       grind)
    | (have r₁ := eq19227
       have r₂ := eq18 (σ x) (σ x)
       grind)
    | (have r₁ := eq19227
       have r₂ := eq18 (k (σ x) (σ x)) (σ x)
       grind)
    | exact resolve eq19227 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19227
  have eq19565 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18242 (σ x)
       have i₂ := eq19266
       grind)
    | exact superpose eq19266 eq18242
    | exact resolve eq18242 eq19266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18242
  have eq19580 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq19266
  have eq19599 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19580
       have i₂ := eq1290
       grind)
    | exact superpose eq1290 eq19580
    | exact resolve eq19580 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq19600 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq19599
  have eq19605 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17226 eq19600
    | exact resolve eq19600 eq17226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17226 eq19600
  have eq19606 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq19605
  have eq19650 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1929 (σ x)
       have i₂ := eq19606
       grind)
    | exact superpose eq19606 eq1929
    | (have j0 := eq1929 (σ x)
       grind)
    | exact resolve eq1929 eq19606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929
  have eq19677 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq19650
  have eq19680 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19565 eq19677
    | exact resolve eq19677 eq19565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19677
  have eq19970 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq821 y (σ x)
       have i₂ := eq19680
       grind)
    | exact superpose eq19680 eq821
    | exact resolve eq821 eq19680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq19680
  have eq20009 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19970
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq19970
    | exact resolve eq19970 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19970
  have eq20060 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1276 y x X0
       have i₂ := eq20009
       grind)
    | exact superpose eq20009 eq1276
    | (have j0 := eq1276 y x x
       grind)
    | exact resolve eq1276 eq20009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276 eq20009
  have eq20067 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1283 eq20060
    | (have j0 := eq20060 X0
       grind)
    | exact resolve eq20060 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq20060
  have eq20091 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (σ y) (σ x)
       have i₂ := eq19565
       grind)
    | exact superpose eq19565 eq16
    | exact resolve eq16 eq19565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21958 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq20091 (σ y)
       have i₂ := eq1280 (σ y)
       grind)
    | exact superpose eq1280 eq20091
    | (have j1 := eq1280 (σ x)
       grind)
    | exact resolve eq20091 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280 eq20091
  have eq21996 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ y)) := by
    first
    | exact superpose eq19565 eq21958
    | exact resolve eq21958 eq19565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19565 eq21958
  have eq22003 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq18765 eq21996
    | exact resolve eq21996 eq18765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21996
  have eq22005 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) := by
    first
    | exact superpose eq19606 eq22003
    | exact resolve eq22003 eq19606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19606 eq22003
  have eq22006 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ x) := by
    first
    | exact superpose eq18765 eq22005
    | exact resolve eq22005 eq18765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22005
  have eq22007 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22006
  have eq24221 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq22007
       have r₂ := eq18145
       grind)
    | exact resolve eq22007 eq18145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18145
  have eq24425 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22007
       have i₂ := eq24221
       grind)
    | exact superpose eq24221 eq22007
    | exact resolve eq22007 eq24221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24430 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq24425
  have eq24602 : y = (M.op (M.op x x) y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20067 x
       have i₂ := eq24430
       grind)
    | exact superpose eq24430 eq20067
    | exact resolve eq20067 eq24430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20067 eq24430
  have eq24796 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24221 eq24602
    | exact resolve eq24602 eq24221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24221 eq24602
  have eq24816 : y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq24796
       have r₂ := eq19580
       grind)
    | exact resolve eq24796 eq19580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19580 eq24796
  have eq25114 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq24816
       grind)
    | exact superpose eq24816 eq9
    | exact resolve eq9 eq24816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24816
  have eq25189 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq25114
       have r₂ := eq18765
       grind)
    | exact resolve eq25114 eq18765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18765 eq25114
  have eq25321 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22007
       have i₂ := eq25189
       grind)
    | exact superpose eq25189 eq22007
    | exact resolve eq22007 eq25189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22007 eq25189
  have eq25326 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25321
  have eq25461 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (σ x)
       have i₂ := eq25326
       grind)
    | exact superpose eq25326 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq25326
       grind)
    | exact resolve eq13 eq25326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25651 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq25461 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25461
  have eq25654 : y = (M.op x x) := by
    first
    | (have r₁ := eq1281
       have r₂ := eq25651 (σ y)
       grind)
    | exact resolve eq1281 eq25651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq25892 : ∀ X0 : G, (M.op (M.op (M.op x X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq25654
       grind)
    | exact superpose eq25654 eq16
    | exact resolve eq16 eq25654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25895 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) y) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 x x X1
       have i₂ := eq25654
       grind)
    | exact superpose eq25654 eq175
    | exact resolve eq175 eq25654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq32958 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25895 X0 X0
       have i₂ := eq25892 X0
       grind)
    | exact superpose eq25892 eq25895
    | exact resolve eq25895 eq25892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25892 eq25895
  have eq38109 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32958 (σ x)
       have i₂ := eq25326
       grind)
    | exact superpose eq25326 eq32958
    | exact resolve eq32958 eq25326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32958
  have eq38150 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq38109
       have i₂ := eq25651 (σ x)
       grind)
    | exact superpose eq25651 eq38109
    | exact resolve eq38109 eq25651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25651 eq38109
  have eq38162 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq15396
       have r₂ := eq38150
       grind)
    | exact resolve eq15396 eq38150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15396
  have eq38173 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38162
       have i₂ := eq38150
       grind)
    | exact superpose eq38150 eq38162
    | exact resolve eq38162 eq38150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38150 eq38162
  have eq38174 : (σ x) = (σ y) := by grind
  clear eq38173
  have eq38311 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq38174
       grind)
    | exact superpose eq38174 eq15
    | exact resolve eq15 eq38174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38392 : x = y := by
    first
    | (have i₁ := eq38311
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq38311
    | exact resolve eq38311 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38311
  have eq38421 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq38392
       grind)
    | exact superpose eq38392 eq9
    | exact resolve eq9 eq38392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38392
  have eq38970 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38421
       have i₂ := eq25654
       grind)
    | exact superpose eq25654 eq38421
    | exact resolve eq38421 eq25654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25654 eq38421
  have eq39012 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq38970
       have i₂ := eq25326
       grind)
    | exact superpose eq25326 eq38970
    | exact resolve eq38970 eq25326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25326 eq38970
  have eq39032 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq39012
       have i₂ := eq38174
       grind)
    | exact superpose eq38174 eq39012
    | (have r₁ := eq39012
       have r₂ := eq38174
       grind)
    | exact resolve eq39012 eq38174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38174 eq39012
  have eq39033 : False := by grind
  exact eq39033

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  clear eq44
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq50
    | exact resolve eq50 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq80 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq79
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq79
    | exact resolve eq79 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq77
    | exact resolve eq77 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq89 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq75 sF3
       grind)
    | exact superpose eq75 eq73
    | exact resolve eq73 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq90 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq89
       have i₂ := eq75 y
       grind)
    | exact superpose eq75 eq89
    | exact resolve eq89 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq89
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq115 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq485 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq14
    | exact resolve eq14 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq14
    | exact resolve eq14 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq584 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq591 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq14
    | exact resolve eq14 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq1142 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq591
    | exact resolve eq591 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq10039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq10038
    | exact resolve eq10038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10038
  have eq10050 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq10039
       have r₂ := eq28
       grind)
    | exact resolve eq10039 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10039
  have eq10054 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq10050 eq115
    | exact resolve eq115 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq10050
  have eq10118 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq10054
    | exact resolve eq10054 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10054
  have eq10119 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10118
  have eq10138 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq485 y X0
       have i₂ := eq10119
       grind)
    | exact superpose eq10119 eq485
    | exact resolve eq485 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq10139 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq486 y X0
       have i₂ := eq10119
       grind)
    | exact superpose eq10119 eq486
    | exact resolve eq486 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq10145 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq591 y X0
       have i₂ := eq10119
       grind)
    | exact superpose eq10119 eq591
    | exact resolve eq591 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq10152 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq10119
       grind)
    | exact superpose eq10119 eq14
    | exact resolve eq14 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10119
  have eq10176 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10152 X0
       have i₂ := eq1142 y X0
       grind)
    | exact superpose eq1142 eq10152
    | exact resolve eq10152 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10152
  have eq10187 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10139 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10139
    | (have j0 := eq10139 X0
       grind)
    | exact resolve eq10139 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10139
  have eq10188 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10138 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10138
    | (have j0 := eq10138 X0
       grind)
    | exact resolve eq10138 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10138
  have eq10201 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10187 x
       have i₂ := eq1142 sF3 x
       grind)
    | exact superpose eq1142 eq10187
    | exact resolve eq10187 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq10187
  have eq19699 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10145 X0
       have i₂ := eq10176 X0
       grind)
    | exact superpose eq10176 eq10145
    | exact resolve eq10145 eq10176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10145
  have eq19759 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq19699 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19699
  have eq19805 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10176 X0
       have i₂ := eq19759 X0
       grind)
    | exact superpose eq19759 eq10176
    | exact resolve eq10176 eq19759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10176 eq19759
  have eq19908 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq19805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19805
  have eq20251 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19908 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19908
    | (have j0 := eq19908 x
       grind)
    | exact resolve eq19908 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19908
  have eq20527 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20251 eq30
    | exact resolve eq30 eq20251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20251
  have eq20657 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq20527
    | exact resolve eq20527 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20527
  have eq20658 : y = (M.op x y) ∨ x = y := by grind
  clear eq20657
  have eq20673 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20658 eq21
    | exact resolve eq21 eq20658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20658
  have eq20807 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20673
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20673
    | exact resolve eq20673 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20673
  have eq321411 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10201 eq10188
    | exact resolve eq10188 eq10201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10188
  have eq321606 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq321411 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321411
  have eq321740 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4⟩ := hcon
    have f321740_16 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (σ x) ∨ y = x := by
      intro X0
      grind
    have f321740_17 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (σ x) ∨ y = x := by
      intro X0
      grind
    have f321740_26 : (σ y) ≠ (M.op X0 (σ y)) := by grind
    have f321740_29 : (σ y) ≠ (σ x) := by grind
    have f321740_30 : y ≠ x := by grind
    have f321740_33 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = x := by
      intro X0
      first
      | (have j0 := f321740_17 X0
         grind)
      | (have r₁ := f321740_17 X0
         have r₂ := f321740_29
         grind)
      | exact resolve f321740_17 f321740_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f321740_34 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = x := by
      intro X0
      first
      | (have j0 := f321740_16 X0
         grind)
      | (have r₁ := f321740_16 X0
         have r₂ := f321740_29
         grind)
      | exact resolve f321740_16 f321740_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f321740_35 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f321740_33 X0
         grind)
      | (have r₁ := f321740_33 X0
         have r₂ := f321740_30
         grind)
      | exact resolve f321740_33 f321740_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f321740_36 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
      intro X0
      first
      | (have j0 := f321740_34 X0
         grind)
      | (have r₁ := f321740_34 X0
         have r₂ := f321740_30
         grind)
      | exact resolve f321740_34 f321740_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f321740_37 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
      intro X0
      first
      | (have i₁ := f321740_36 X0
         have i₂ := f321740_35 X0
         grind)
      | exact superpose f321740_35 f321740_36
      | exact resolve f321740_36 f321740_35
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f321740_38 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f321740_26
         have i₂ := f321740_37 X0
         grind)
      | exact superpose f321740_37 f321740_26
      | (have r₁ := f321740_26
         have r₂ := f321740_37 X0
         grind)
      | exact resolve f321740_26 f321740_37
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f321740_39 : False := by grind
    exact f321740_39
  clear eq10201 eq321606
  have eq322219 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq321740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321740
  have eq322355 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq322219
    | (have j0 := eq322219 (σ x)
       grind)
    | exact resolve eq322219 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322219
  have eq323677 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq322355 eq28
    | exact resolve eq28 eq322355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322355
  have eq323789 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq323677
       have r₂ := eq20807
       grind)
    | exact resolve eq323677 eq20807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20807 eq323677
  have eq323792 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq323789 eq30
    | exact resolve eq30 eq323789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq323789
  have eq324797 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq323792
    | exact resolve eq323792 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq323792
  have eq324798 : x = y := by grind
  clear eq324797
  have eq324817 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq324798
       grind)
    | exact superpose eq324798 eq19
    | exact resolve eq19 eq324798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq324818 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq324798
       grind)
    | exact superpose eq324798 eq25
    | exact resolve eq25 eq324798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq324798
  have eq325169 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq324818
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq324818
    | exact resolve eq324818 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq324818
  have eq325201 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq325169 eq27
    | exact resolve eq27 eq325169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq325169
  have eq328114 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq325201 eq80
    | exact resolve eq80 eq325201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq325201
  have eq328308 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq328114
       have i₂ := eq324817
       grind)
    | exact superpose eq324817 eq328114
    | exact resolve eq328114 eq324817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324817 eq328114
  have eq328320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq328308 eq15
    | exact resolve eq15 eq328308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328308
  have eq328727 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq328320
    | exact resolve eq328320 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq328320
  have eq328848 : False := by grind
  exact eq328848
