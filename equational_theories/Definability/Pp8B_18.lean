import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq72
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq80
    | exact resolve eq80 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq325 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq65 (τ X0)
       grind)
    | exact superpose eq65 eq39
    | exact resolve eq39 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq344 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq325 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq325
    | exact resolve eq325 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq406 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0) X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq53
  have eq550 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq54
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq54 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq562 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq3258 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq418
    | exact resolve eq418 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq3284 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3258 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3258
    | (have j0 := eq3258 y x
       grind)
    | exact resolve eq3258 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3286 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3258
    | (have j0 := eq3258 (σ y) (σ x)
       grind)
    | exact resolve eq3258 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3433 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq423 x X1 X0
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq423
    | exact resolve eq423 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq3481 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3433 sF0 sF0
       have i₂ := eq54 sF0
       grind)
    | exact superpose eq54 eq3433
    | exact resolve eq3433 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq3433
  have eq3672 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq562 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq562
    | (have j0 := eq562 (τ X0)
       grind)
    | exact resolve eq562 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq3692 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3672 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3672
    | (have j0 := eq3672 X0
       grind)
    | exact resolve eq3672 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672
  have eq3704 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq3756 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq414 (M.op y X0) X0
       have i₂ := eq56 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq56 eq414
    | exact resolve eq414 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq6734 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq56 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq56 eq406
    | exact resolve eq406 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq11993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq83 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11993
    | exact resolve eq11993 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11993
  have eq12005 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq11994
       have r₂ := eq28
       grind)
    | exact resolve eq11994 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11994
  have eq12007 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12005
    | exact resolve eq12005 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12005
  have eq12033 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12007 eq3258
    | exact resolve eq3258 eq12007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12007
  have eq12034 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12033
    | exact resolve eq12033 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12033
  have eq12035 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12034
  have eq12064 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3258 y y
       have i₂ := eq12035
       grind)
    | exact superpose eq12035 eq3258
    | exact resolve eq3258 eq12035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12035
  have eq12065 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12064
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12064
    | exact resolve eq12064 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12064
  have eq12066 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12065
  have eq12080 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12066 eq3286
    | exact resolve eq3286 eq12066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286
  have eq12088 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12080
    | exact resolve eq12080 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12080
  have eq12216 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12088 eq65
    | exact resolve eq65 eq12088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12407 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12066 eq12216
    | exact resolve eq12216 eq12066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12066 eq12216
  have eq12415 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12407
  have eq12885 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12415 eq83
    | exact resolve eq83 eq12415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq12415
  have eq12898 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12885
  have eq14621 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3258 y y
       have i₂ := eq12898
       grind)
    | exact superpose eq12898 eq3258
    | exact resolve eq3258 eq12898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12898
  have eq14622 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14621
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14621
    | exact resolve eq14621 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14621
  have eq14623 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq14622
  have eq14630 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14623 eq30
    | exact resolve eq30 eq14623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14632 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14623 eq41
    | exact resolve eq41 eq14623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq14703 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14623 eq12088
    | exact resolve eq12088 eq14623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12088
  have eq14744 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq14703
  have eq14802 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq42 eq14632
    | exact resolve eq14632 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14632
  have eq14804 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq14630
    | exact resolve eq14630 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14630
  have eq14869 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14804 eq3481
    | exact resolve eq3481 eq14804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3481
  have eq14872 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq19716 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3756 x
       have i₂ := eq14869
       grind)
    | exact superpose eq14869 eq3756
    | exact resolve eq3756 eq14869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756 eq14869
  have eq19782 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19716
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq19716
    | exact resolve eq19716 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19716
  have eq21048 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19782 eq14
    | exact resolve eq14 eq19782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19782
  have eq34487 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14802 eq35
    | exact resolve eq35 eq14802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14802
  have eq34645 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq34487
    | (have j0 := eq34487 X0
       grind)
    | exact resolve eq34487 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34487
  have eq34683 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34645 X0
       have i₂ := eq35 X0 y
       grind)
    | exact superpose eq35 eq34645
    | exact resolve eq34645 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq34645
  have eq34704 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34683 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34683
    | (have j0 := eq34683 X0
       grind)
    | exact resolve eq34683 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34683
  have eq35027 : (σ y) = (k (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34704 eq344
    | exact resolve eq344 eq34704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq34704
  have eq35106 : (σ y) = (σ (k (M.op (τ (σ y)) (τ (σ y))) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq35027
    | exact resolve eq35027 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq35027
  have eq35161 : (σ y) = (σ (k (M.op y y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq35106
    | exact resolve eq35106 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35106
  have eq35663 : (τ (σ y)) = (k (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35161 eq16
    | exact resolve eq16 eq35161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35161
  have eq35740 : y = (k (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq35663
    | exact resolve eq35663 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35663
  have eq126475 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21048 eq6734
    | exact resolve eq6734 eq21048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6734 eq21048
  have eq126824 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14804 eq126475
    | exact resolve eq126475 eq14804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14804 eq126475
  have eq126886 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126824
       have r₂ := eq14872
       grind)
    | exact resolve eq126824 eq14872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14872 eq126824
  have eq126887 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126886
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq126886
    | exact resolve eq126886 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126886
  have eq126898 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35740
       have i₂ := eq126887
       grind)
    | exact superpose eq126887 eq35740
    | exact resolve eq35740 eq126887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35740 eq126887
  have eq126940 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq126898
  have eq127265 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126940 eq557
    | (have j0 := eq557 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq557 eq126940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq126940
  have eq127269 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq127265
  have eq127290 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq127269
    | exact resolve eq127269 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127269
  have eq127319 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127290
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq127290
    | exact resolve eq127290 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127290
  have eq127331 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq127319
       have r₂ := eq14623
       grind)
    | exact resolve eq127319 eq14623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14623 eq127319
  have eq127340 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq127331
    | exact resolve eq127331 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127331
  have eq130569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127340 eq14744
    | exact resolve eq14744 eq127340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14744 eq127340
  have eq130721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq130569
  have eq130733 : x = (M.op x y) := by
    first
    | (have r₁ := eq130721
       have r₂ := eq28
       grind)
    | exact resolve eq130721 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130721
  have eq131402 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq130733 eq21
    | exact resolve eq21 eq130733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq131542 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq130733 eq3284
    | exact resolve eq3284 eq130733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284
  have eq131556 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq131542
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq131542
    | exact resolve eq131542 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq131542
  have eq131684 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq131402
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq131402
    | exact resolve eq131402 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131402
  have eq131685 : x = (M.op y y) := by
    first
    | exact superpose eq130733 eq131556
    | exact resolve eq131556 eq130733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130733 eq131556
  have eq131686 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq131684 eq27
    | exact resolve eq27 eq131684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq132075 : y = (k x y) := by
    first
    | (have i₁ := eq65 y
       have i₂ := eq131685
       grind)
    | exact superpose eq131685 eq65
    | exact resolve eq65 eq131685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132087 : y = (M.op x x) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq131685
       grind)
    | exact superpose eq131685 eq56
    | exact resolve eq56 eq131685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq131685
  have eq132261 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq132075
       grind)
    | exact superpose eq132075 eq45
    | exact resolve eq45 eq132075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq132075
  have eq132312 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq131684 eq132261
    | exact resolve eq132261 eq131684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132261
  have eq132331 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq132312
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq132312
    | exact resolve eq132312 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132312
  have eq132495 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq132087
       grind)
    | exact superpose eq132087 eq78
    | exact resolve eq78 eq132087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq132087
  have eq132555 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq131684 eq132495
    | exact resolve eq132495 eq131684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132495
  have eq132562 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq132555
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq132555
    | exact resolve eq132555 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132555
  have eq132687 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq132331 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq132331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132331
  have eq132695 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq131686 eq132687
    | exact resolve eq132687 eq131686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132687
  have eq132708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq131686 eq132695
    | exact resolve eq132695 eq131686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132695
  have eq132721 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq132708
       have r₂ := eq28
       grind)
    | exact resolve eq132708 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132708
  have eq141139 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq132562 eq3704
    | (have j0 := eq3704 (σ (M.op x y))
       grind)
    | exact resolve eq3704 eq132562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq141157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq131686 eq141139
    | exact resolve eq141139 eq131686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141139
  have eq141168 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq141157
       have r₂ := eq28
       grind)
    | exact resolve eq141157 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141157
  have eq141466 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq132721 eq3258
    | exact resolve eq3258 eq132721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3258 eq132721
  have eq141476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq131686 eq141466
    | exact resolve eq141466 eq131686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131686 eq141466
  have eq141483 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq141476
       have r₂ := eq28
       grind)
    | exact resolve eq141476 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141476
  have eq141605 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq141483 eq28
    | exact resolve eq28 eq141483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq141483
  have eq142803 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq141168 eq65
    | exact resolve eq65 eq141168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq141168
  have eq144083 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq142803 eq132562
    | exact resolve eq132562 eq142803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132562 eq142803
  have eq144126 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq144083
  have eq144137 : x = y := by
    first
    | (have r₁ := eq144126
       have r₂ := eq141605
       grind)
    | exact resolve eq144126 eq141605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144126
  have eq144168 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq144137
       grind)
    | exact superpose eq144137 eq25
    | exact resolve eq25 eq144137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq144137
  have eq144535 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq144168
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq144168
    | exact resolve eq144168 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq144168
  have eq144673 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq131684 eq144535
    | exact resolve eq144535 eq131684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131684 eq144535
  have eq144754 : False := by grind
  exact eq144754

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq75 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq75
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq72
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  clear eq87
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq247 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq550 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq54
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq54 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq562 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq567 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq555
    | (have j0 := eq555 X0 X1
       grind)
    | exact resolve eq555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq3257 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq418
    | exact resolve eq418 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq418
  have eq3285 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3257
    | (have j0 := eq3257 (σ y) (σ x)
       grind)
    | exact resolve eq3257 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3704 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq562 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq562
    | (have j0 := eq562 (τ X0)
       grind)
    | exact resolve eq562 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq562
  have eq3725 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3704 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3704
    | (have j0 := eq3704 X0
       grind)
    | exact resolve eq3704 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq3737 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3725 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3725
    | (have j0 := eq3725 X0
       grind)
    | exact resolve eq3725 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq23639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq23640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23639
    | exact resolve eq23639 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23639
  have eq23651 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23640
       have r₂ := eq28
       grind)
    | exact resolve eq23640 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23640
  have eq23678 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23651 eq3257
    | exact resolve eq3257 eq23651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24996 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23678 eq23651
    | exact resolve eq23651 eq23678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23651 eq23678
  have eq25031 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq24996
  have eq25045 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25031 eq54
    | exact resolve eq54 eq25031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25031
  have eq25075 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25045
    | exact resolve eq25045 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25045
  have eq25105 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3257 x y
       have i₂ := eq25075
       grind)
    | exact superpose eq25075 eq3257
    | exact resolve eq3257 eq25075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3257
  have eq26855 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25075
       have i₂ := eq25105
       grind)
    | exact superpose eq25105 eq25075
    | exact resolve eq25075 eq25105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25075 eq25105
  have eq26892 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26855
  have eq26899 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq26892
       grind)
    | exact superpose eq26892 eq78
    | exact resolve eq78 eq26892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq26908 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq26892
       grind)
    | exact superpose eq26892 eq54
    | exact resolve eq54 eq26892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq26910 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq26892
       grind)
    | exact superpose eq26892 eq65
    | exact resolve eq65 eq26892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26892
  have eq26940 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26908
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26908
    | exact resolve eq26908 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26908
  have eq26942 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26899
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26899
    | exact resolve eq26899 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26899
  have eq26947 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26940 eq247
    | exact resolve eq247 eq26940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq26953 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26940 eq3285
    | exact resolve eq3285 eq26940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq27004 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq26953
    | exact resolve eq26953 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26953
  have eq28473 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27004 eq26947
    | exact resolve eq26947 eq27004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26947 eq27004
  have eq28511 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq28473
  have eq28516 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26940 eq28511
    | exact resolve eq28511 eq26940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26940 eq28511
  have eq28546 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq28516
  have eq28550 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28546 eq77
    | exact resolve eq77 eq28546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq28546
  have eq28593 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq28550
    | exact resolve eq28550 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28550
  have eq31838 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26942 eq50
    | exact resolve eq50 eq26942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31857 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26942 eq3737
    | (have j0 := eq3737 (σ x)
       grind)
    | exact resolve eq3737 eq26942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26942
  have eq31870 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq31857
    | exact resolve eq31857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31857
  have eq31871 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31870
  have eq31880 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq31838
    | exact resolve eq31838 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31838
  have eq31947 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq31871 eq65
    | exact resolve eq65 eq31871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31871
  have eq32176 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq31947 eq50
    | exact resolve eq50 eq31947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31947
  have eq32227 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq32176
    | exact resolve eq32176 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32176
  have eq32390 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq31880
       have i₂ := eq32227
       grind)
    | exact superpose eq32227 eq31880
    | exact resolve eq31880 eq32227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31880 eq32227
  have eq32414 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq32390
  have eq32438 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq32414 eq28
    | exact resolve eq28 eq32414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32414
  have eq37985 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3737 x
       have i₂ := eq28593
       grind)
    | exact superpose eq28593 eq3737
    | (have j0 := eq3737 x
       grind)
    | exact resolve eq3737 eq28593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3737
  have eq38004 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37985
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37985
    | exact resolve eq37985 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37985
  have eq38005 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq38004
  have eq38908 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq38005
       grind)
    | exact superpose eq38005 eq65
    | exact resolve eq65 eq38005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38005
  have eq39328 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28593
       have i₂ := eq38908
       grind)
    | exact superpose eq38908 eq28593
    | exact resolve eq28593 eq38908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28593 eq38908
  have eq39354 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq39328
  have eq39643 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39354 eq30
    | exact resolve eq30 eq39354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39354
  have eq39914 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq39643
    | exact resolve eq39643 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39643
  have eq39915 : x = (M.op x y) ∨ x = y := by grind
  clear eq39914
  have eq39916 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq39915 eq21
    | exact resolve eq21 eq39915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39915
  have eq40133 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq39916
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39916
    | exact resolve eq39916 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39916
  have eq40134 : x = y := by
    first
    | (have r₁ := eq40133
       have r₂ := eq32438
       grind)
    | exact resolve eq40133 eq32438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32438 eq40133
  have eq40135 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq40134
       grind)
    | exact superpose eq40134 eq19
    | exact resolve eq19 eq40134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40136 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq40134
       grind)
    | exact superpose eq40134 eq25
    | exact resolve eq25 eq40134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq40267 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26910
       have i₂ := eq40134
       grind)
    | exact superpose eq40134 eq26910
    | exact resolve eq26910 eq40134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26910 eq40134
  have eq40361 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40136
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40136
    | exact resolve eq40136 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40136
  have eq40366 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40361 eq27
    | exact resolve eq27 eq40361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40361
  have eq40763 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq40366 eq65
    | exact resolve eq65 eq40366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq43965 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq567 x x
       have i₂ := eq40267
       grind)
    | exact superpose eq40267 eq567
    | (have j0 := eq567 x x
       grind)
    | exact resolve eq567 eq40267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq40267
  have eq43974 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43965
  have eq43975 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43974
  have eq43987 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43975
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43975
    | exact resolve eq43975 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43975
  have eq44009 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40366 eq43987
    | exact resolve eq43987 eq40366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40366 eq43987
  have eq44010 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44009
  have eq44029 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq44010 eq28
    | exact resolve eq28 eq44010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq44112 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq44010 eq40763
    | exact resolve eq40763 eq44010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40763 eq44010
  have eq44805 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq44112 eq50
    | exact resolve eq50 eq44112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq44112
  have eq44865 : x = (k x x) := by
    first
    | exact superpose eq29 eq44805
    | exact resolve eq44805 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44805
  have eq44906 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq44865
       grind)
    | exact superpose eq44865 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq44865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44865
  have eq44907 : x = (M.op x x) := by grind
  clear eq44906
  have eq44922 : x = (M.op x y) := by
    first
    | (have i₁ := eq44907
       have i₂ := eq40135
       grind)
    | exact superpose eq40135 eq44907
    | exact resolve eq44907 eq40135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40135 eq44907
  have eq44959 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq44922 eq21
    | exact resolve eq21 eq44922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq44922
  have eq45235 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44959
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44959
    | exact resolve eq44959 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq44959
  have eq45314 : False := by grind
  exact eq45314

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_x_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq65 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq65
    | exact resolve eq65 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq68
    | exact resolve eq68 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq69
    | exact resolve eq69 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq246 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y) (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq574 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq579 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq574 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq586 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq579 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq579 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq579 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq579 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq595 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq586 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq586
    | (have j0 := eq586 X0 X1
       grind)
    | exact resolve eq586 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq3390 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq427
    | exact resolve eq427 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq3416 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3390 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3390
    | (have j0 := eq3390 y x
       grind)
    | exact resolve eq3390 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3418 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3390
    | (have j0 := eq3390 (σ y) (σ x)
       grind)
    | exact resolve eq3390 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7392 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq595
  have eq7499 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7392 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7392
  have eq7500 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7499
  have eq7861 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7500 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7500
    | exact resolve eq7500 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7951 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq7500 X0
       grind)
    | exact superpose eq7500 eq50
    | exact resolve eq50 eq7500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7500
  have eq8536 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq7861 X0
       grind)
    | exact superpose eq7861 eq16
    | exact resolve eq16 eq7861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7861
  have eq8813 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq8536 X0
       grind)
    | exact superpose eq8536 eq50
    | exact resolve eq50 eq8536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq8536
  have eq13103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq70 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq13104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq13103
    | exact resolve eq13103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13103
  have eq13117 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq13104
       have r₂ := eq28
       grind)
    | exact resolve eq13104 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13104
  have eq13120 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq13117
    | exact resolve eq13117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13117
  have eq13150 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq13120 eq3390
    | exact resolve eq3390 eq13120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13120
  have eq13151 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq13150
    | exact resolve eq13150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13150
  have eq13152 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13151
  have eq13189 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3390 y y
       have i₂ := eq13152
       grind)
    | exact superpose eq13152 eq3390
    | exact resolve eq3390 eq13152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390 eq13152
  have eq13190 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13189
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13189
    | exact resolve eq13189 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13189
  have eq13191 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13190
  have eq13212 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13191 eq3418
    | exact resolve eq3418 eq13191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3418
  have eq13220 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13212
    | exact resolve eq13212 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13212
  have eq13358 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13220 eq246
    | exact resolve eq246 eq13220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq13220
  have eq13528 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13191 eq13358
    | exact resolve eq13358 eq13191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13191 eq13358
  have eq13562 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13528
  have eq14039 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13562 eq8813
    | exact resolve eq8813 eq13562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8813 eq13562
  have eq14054 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14039
    | exact resolve eq14039 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14039
  have eq14057 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq14054
    | exact resolve eq14054 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14054
  have eq14058 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14057
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14057
    | exact resolve eq14057 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14057
  have eq14059 : x = (M.op x y) := by grind
  clear eq14058
  have eq14199 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq14059 eq21
    | exact resolve eq21 eq14059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq14257 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq14059 eq3416
    | exact resolve eq3416 eq14059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416
  have eq14267 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq14257
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14257
    | exact resolve eq14257 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq14257
  have eq14317 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14199
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14199
    | exact resolve eq14199 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14199
  have eq14318 : x = (M.op y y) := by
    first
    | exact superpose eq14059 eq14267
    | exact resolve eq14267 eq14059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14059 eq14267
  have eq14465 : y = (M.op x x) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq14318
       grind)
    | exact superpose eq14318 eq52
    | exact resolve eq52 eq14318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq14318
  have eq14714 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7951 x
       have i₂ := eq14465
       grind)
    | exact superpose eq14465 eq7951
    | exact resolve eq7951 eq14465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7951 eq14465
  have eq14733 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14714
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14714
    | exact resolve eq14714 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq14714
  have eq14742 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14733
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14733
    | exact resolve eq14733 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14733
  have eq14747 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq14742
    | exact resolve eq14742 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14742
  have eq14749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14317 eq14747
    | exact resolve eq14747 eq14317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14317 eq14747
  have eq14751 : False := by grind
  exact eq14751

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_y_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq64
  have eq74 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq56
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq74
  have eq91 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq246 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y) (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq597 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq50
    | (have j1 := eq61 X0 X0
       grind)
    | exact resolve eq50 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq611 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq615 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X1) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq603
    | (have j0 := eq603 X0 X1
       grind)
    | exact resolve eq603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq3335 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq460 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq460
    | exact resolve eq460 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq460
  have eq3363 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3335
    | (have j0 := eq3335 (σ y) (σ x)
       grind)
    | exact resolve eq3335 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3784 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq611 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq611
    | (have j0 := eq611 (τ X0)
       grind)
    | exact resolve eq611 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq611
  have eq3805 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3784 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3784
    | (have j0 := eq3784 X0
       grind)
    | exact resolve eq3784 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3784
  have eq3818 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3805 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3805
    | (have j0 := eq3805 X0
       grind)
    | exact resolve eq3805 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq23950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq23951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23950
    | exact resolve eq23950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23950
  have eq23962 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23951
       have r₂ := eq28
       grind)
    | exact resolve eq23951 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23951
  have eq23989 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23962 eq3335
    | exact resolve eq3335 eq23962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25305 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23989 eq23962
    | exact resolve eq23962 eq23989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23962 eq23989
  have eq25340 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq25305
  have eq25355 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25340 eq50
    | exact resolve eq50 eq25340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25340
  have eq25384 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25355
    | exact resolve eq25355 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25355
  have eq25414 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3335 x y
       have i₂ := eq25384
       grind)
    | exact superpose eq25384 eq3335
    | exact resolve eq3335 eq25384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3335
  have eq27166 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25384
       have i₂ := eq25414
       grind)
    | exact superpose eq25414 eq25384
    | exact resolve eq25384 eq25414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25384 eq25414
  have eq27203 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27166
  have eq27210 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq27203
       grind)
    | exact superpose eq27203 eq67
    | exact resolve eq67 eq27203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq27219 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq27220 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq27203
       grind)
    | exact superpose eq27203 eq50
    | exact resolve eq50 eq27203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq27203
  have eq27251 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27220
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27220
    | exact resolve eq27220 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27220
  have eq27253 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27210
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27210
    | exact resolve eq27210 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27210
  have eq27258 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27251 eq246
    | exact resolve eq246 eq27251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq27264 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27251 eq3363
    | exact resolve eq3363 eq27251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363
  have eq27315 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq27264
    | exact resolve eq27264 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27264
  have eq28783 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27315 eq27258
    | exact resolve eq27258 eq27315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27258 eq27315
  have eq28821 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq28783
  have eq28826 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27251 eq28821
    | exact resolve eq28821 eq27251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27251 eq28821
  have eq28856 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq28826
  have eq28859 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28856 eq76
    | exact resolve eq76 eq28856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq28856
  have eq28902 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq28859
    | exact resolve eq28859 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28859
  have eq31422 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27253 eq56
    | exact resolve eq56 eq27253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31441 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27253 eq3818
    | (have j0 := eq3818 (σ x)
       grind)
    | exact resolve eq3818 eq27253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27253
  have eq31454 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq31441
    | exact resolve eq31441 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31441
  have eq31455 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31454
  have eq31464 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq31422
    | exact resolve eq31422 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31422
  have eq31529 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31455
  have eq32498 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq31529 eq56
    | exact resolve eq56 eq31529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31529
  have eq32549 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq32498
    | exact resolve eq32498 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32498
  have eq32712 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq31464
       have i₂ := eq32549
       grind)
    | exact superpose eq32549 eq31464
    | exact resolve eq31464 eq32549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31464 eq32549
  have eq32736 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq32712
  have eq32760 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq32736 eq28
    | exact resolve eq28 eq32736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32736
  have eq37785 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3818 x
       have i₂ := eq28902
       grind)
    | exact superpose eq28902 eq3818
    | (have j0 := eq3818 x
       grind)
    | exact resolve eq3818 eq28902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3818
  have eq37804 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37785
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37785
    | exact resolve eq37785 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37785
  have eq37805 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq37804
  have eq38969 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq37805
  have eq39389 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28902
       have i₂ := eq38969
       grind)
    | exact superpose eq38969 eq28902
    | exact resolve eq28902 eq38969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28902 eq38969
  have eq39415 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq39389
  have eq39440 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39415 eq30
    | exact resolve eq30 eq39415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39415
  have eq39711 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq39440
    | exact resolve eq39440 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39440
  have eq39712 : x = (M.op x y) ∨ x = y := by grind
  clear eq39711
  have eq39713 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq39712 eq21
    | exact resolve eq21 eq39712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39712
  have eq39930 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq39713
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39713
    | exact resolve eq39713 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39713
  have eq39931 : x = y := by
    first
    | (have r₁ := eq39930
       have r₂ := eq32760
       grind)
    | exact resolve eq39930 eq32760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32760 eq39930
  have eq40200 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq39931
       grind)
    | exact superpose eq39931 eq19
    | exact resolve eq19 eq39931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40201 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39931
       grind)
    | exact superpose eq39931 eq25
    | exact resolve eq25 eq39931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq40331 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27219
       have i₂ := eq39931
       grind)
    | exact superpose eq39931 eq27219
    | exact resolve eq27219 eq39931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27219 eq39931
  have eq40426 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40201
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40201
    | exact resolve eq40201 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40201
  have eq40429 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40426 eq27
    | exact resolve eq27 eq40426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40426
  have eq41238 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq43877 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq615 x x
       have i₂ := eq40331
       grind)
    | exact superpose eq40331 eq615
    | (have j0 := eq615 x x
       grind)
    | exact resolve eq615 eq40331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq40331
  have eq43886 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43877
  have eq43887 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43886
  have eq43899 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43887
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43887
    | exact resolve eq43887 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43887
  have eq43921 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40429 eq43899
    | exact resolve eq43899 eq40429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40429 eq43899
  have eq43922 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43921
  have eq43941 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq43922 eq28
    | exact resolve eq28 eq43922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq44023 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq43922 eq41238
    | exact resolve eq41238 eq43922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41238 eq43922
  have eq45298 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq44023 eq56
    | exact resolve eq56 eq44023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq44023
  have eq45358 : x = (k x x) := by
    first
    | exact superpose eq29 eq45298
    | exact resolve eq45298 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq45298
  have eq45397 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq45358
       grind)
    | exact superpose eq45358 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq45358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45358
  have eq45398 : x = (M.op x x) := by grind
  clear eq45397
  have eq45413 : x = (M.op x y) := by
    first
    | (have i₁ := eq45398
       have i₂ := eq40200
       grind)
    | exact superpose eq40200 eq45398
    | exact resolve eq45398 eq40200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40200 eq45398
  have eq45452 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq45413 eq21
    | exact resolve eq21 eq45413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq45413
  have eq45730 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq45452
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45452
    | exact resolve eq45452 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq45452
  have eq45809 : False := by grind
  exact eq45809

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_x_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq47 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq62 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
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
  have eq65 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq65
    | exact resolve eq65 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq68
    | exact resolve eq68 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq69
    | exact resolve eq69 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
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
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq94
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq16
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq121 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq114
  have eq183 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq120
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq183
  have eq244 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq52 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52
    | (have j0 := eq52 y x
       grind)
    | exact resolve eq52 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y) (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq277 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq416 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X0 X0) X0 X1 X2
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq49
    | (have j0 := eq49 y x X0 X1
       grind)
    | exact resolve eq49 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq49
    | (have j0 := eq49 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq49 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 (M.op X1 X0) X1 X2 (M.op X0 X0)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq49
    | exact resolve eq49 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq49 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq49 X0 X1 X2 X3
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq436 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X2 (M.op X0 X1) X1
       have i₂ := eq52 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq52 eq49
    | exact resolve eq49 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq460 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq277
    | exact resolve eq277 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq577 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq582 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq577 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq589 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq582 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq582 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq582 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq582 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq598 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq589
    | (have j0 := eq589 X0 X1
       grind)
    | exact resolve eq589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq3393 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq429 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq429
    | exact resolve eq429 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3422 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3393
    | (have j0 := eq3393 (σ y) (σ x)
       grind)
    | exact resolve eq3393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3572 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq434 x X1 X0
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq434
    | exact resolve eq434 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq3604 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq436 sF2 X1 x
       have i₂ := eq52 sF2 sF2
       grind)
    | exact superpose eq52 eq436
    | exact resolve eq436 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq3622 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3572 sF0 sF0
       have i₂ := eq50 sF0
       grind)
    | exact superpose eq50 eq3572
    | exact resolve eq3572 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3572
  have eq3646 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3622 eq14
    | exact resolve eq14 eq3622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3790 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq425 (M.op y X0) X0
       have i₂ := eq52 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq52 eq425
    | exact resolve eq425 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq3808 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq3604 sF4 sF4
       have i₂ := eq50 sF4
       grind)
    | exact superpose eq50 eq3604
    | exact resolve eq3604 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3604
  have eq3830 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3808 eq14
    | exact resolve eq14 eq3808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3845 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq427 (M.op sF3 x) x
       have i₂ := eq52 (M.op sF3 x) (M.op sF3 x)
       grind)
    | exact superpose eq52 eq427
    | exact resolve eq427 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq3919 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq432 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq432
    | exact resolve eq432 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3970 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq432 X0 X0 X2 X3 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq432
    | exact resolve eq432 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq4138 : (M.op x y) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq3646 x
       have i₂ := eq50 x
       grind)
    | exact superpose eq50 eq3646
    | exact resolve eq3646 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646
  have eq4303 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3830 sF2
       have i₂ := eq50 sF2
       grind)
    | exact superpose eq50 eq3830
    | exact resolve eq3830 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3830
  have eq5013 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq6127 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq579 (τ X0) (τ X1)
       have i₂ := eq460 X1 X0
       grind)
    | exact superpose eq460 eq579
    | (have j0 := eq579 (τ X0) (τ X1)
       grind)
    | exact resolve eq579 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq579
  have eq6313 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6127 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq6127
    | (have j0 := eq6127 X0 X1
       grind)
    | exact resolve eq6127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6127
  have eq6400 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6313 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq6313
    | (have j0 := eq6313 X0 X1
       grind)
    | exact resolve eq6313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6313
  have eq6483 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6400 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6400
    | (have j0 := eq6400 X0 X1
       grind)
    | exact resolve eq6400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6400
  have eq6565 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6483 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6483
    | (have j0 := eq6483 X0 X1
       grind)
    | exact resolve eq6483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6483
  have eq6646 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6565 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6565
    | (have j0 := eq6565 X0 X1
       grind)
    | exact resolve eq6565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6565
  have eq6654 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6646 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6646
    | (have j0 := eq6646 X0 X1
       grind)
    | exact resolve eq6646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6646
  have eq6948 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 X1 (M.op X0 X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq416
    | exact resolve eq416 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6950 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416 X0 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq429 X0 X1 X0
       grind)
    | exact superpose eq429 eq416
    | exact resolve eq416 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq6996 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) ≠ (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) ∨ (M.op (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) = X1 ∨ (M.op (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) = (k X1 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))
       have i₂ := eq416 X1 X0 X2
       grind)
    | exact superpose eq416 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))
       grind)
    | exact resolve eq12 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq7013 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = X1 ∨ (M.op X0 (M.op (M.op X1 X1) X2)) ≠ (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) ∨ (M.op (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) = (k X1 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6996 X0 X1 X2
       have i₂ := eq52 (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq52 eq6996
    | (have j0 := eq6996 X0 X1 X2
       grind)
    | exact resolve eq6996 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6996
  have eq7016 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) ≠ (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) ∨ (M.op X0 (M.op (M.op X1 X1) X2)) = X1 ∨ (M.op X0 (M.op (M.op X1 X1) X2)) = (k X1 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7013 X0 X1 X2
       have i₂ := eq52 (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq52 eq7013
    | (have j0 := eq7013 X0 X1 X2
       grind)
    | exact resolve eq7013 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7013
  have eq7407 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq598
  have eq7512 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7407 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7407
  have eq8243 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq431 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq50 (M.op X1 X2)
       grind)
    | exact superpose eq50 eq431
    | exact resolve eq431 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq12011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq70 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12011
    | exact resolve eq12011 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12011
  have eq12023 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12012
       have r₂ := eq28
       grind)
    | exact resolve eq12012 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12012
  have eq12025 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12023
    | exact resolve eq12023 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12023
  have eq12033 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  have eq12053 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12025 eq3393
    | exact resolve eq3393 eq12025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12025
  have eq12054 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12053
    | exact resolve eq12053 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12053
  have eq12064 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12054
  have eq12340 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq12064
       grind)
    | exact superpose eq12064 eq45
    | exact resolve eq45 eq12064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq12064
  have eq12363 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12340
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12340
    | exact resolve eq12340 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12340
  have eq12717 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12363 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12363
  have eq12721 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12717
    | exact resolve eq12717 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12717
  have eq12722 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12721
  have eq12734 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12722
    | exact resolve eq12722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12722
  have eq12735 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12734
  have eq12907 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12735 eq3393
    | exact resolve eq3393 eq12735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12735
  have eq12908 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12907
    | exact resolve eq12907 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12907
  have eq12909 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12908
  have eq12914 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12909 eq28
    | exact resolve eq28 eq12909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12915 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12909 eq48
    | exact resolve eq48 eq12909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq12929 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12909 eq4303
    | exact resolve eq4303 eq12909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303
  have eq12930 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq13396 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12915
    | (have j0 := eq12915 (σ x)
       grind)
    | exact resolve eq12915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12915
  have eq13426 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12909 eq13396
    | exact resolve eq13396 eq12909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13396
  have eq13449 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13426
  have eq13454 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13449
       have r₂ := eq12930
       grind)
    | exact resolve eq13449 eq12930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13449
  have eq13939 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12033 eq70
    | exact resolve eq70 eq12033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12033
  have eq13953 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13939
  have eq13964 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq13953
       grind)
    | exact superpose eq13953 eq121
    | exact resolve eq121 eq13953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13974 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq246 y x
       have i₂ := eq13953
       grind)
    | exact superpose eq13953 eq246
    | exact resolve eq246 eq13953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq13953
  have eq13996 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13964
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13964
    | exact resolve eq13964 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13964
  have eq15912 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3393 y (M.op x x)
       have i₂ := eq13974 x
       grind)
    | exact superpose eq13974 eq3393
    | exact resolve eq3393 eq13974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393 eq13974
  have eq15919 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15912
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15912
    | exact resolve eq15912 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15912
  have eq15923 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq15919
       grind)
    | exact superpose eq15919 eq121
    | exact resolve eq121 eq15919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15919
  have eq15961 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15923
  have eq15970 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq15961
    | exact resolve eq15961 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961
  have eq18953 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13996 eq15970
    | exact resolve eq15970 eq13996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13996 eq15970
  have eq18971 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq18953
  have eq18996 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq18971 eq3808
    | exact resolve eq3808 eq18971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq19487 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq18996 eq3845
    | exact resolve eq3845 eq18996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18996
  have eq19567 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq19487
       have i₂ := eq52 sF2 sF2
       grind)
    | exact superpose eq52 eq19487
    | exact resolve eq19487 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19487
  have eq19568 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq18971 eq19567
    | exact resolve eq19567 eq18971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19567
  have eq19603 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq19568
  have eq19928 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3970 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq3970
    | exact resolve eq3970 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20538 : ∀ X0 : G, (M.op (M.op X0 y) (M.op X0 y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq3790 (M.op (M.op x y) (M.op x y))
       have i₂ := eq6948 y x
       grind)
    | exact superpose eq6948 eq3790
    | exact resolve eq3790 eq6948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25713 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6948 X2 X1
       have i₂ := eq453 X1 X2 X0
       grind)
    | (have i₁ := eq6948 X1 X1
       have i₂ := eq453 X1 X1 X1
       grind)
    | exact superpose eq453 eq6948
    | exact resolve eq6948 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq6948
  have eq38235 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (M.op (σ y) X0) (M.op (σ y) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12929 eq8243
    | exact resolve eq8243 eq12929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8243
  have eq38597 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3845 eq38235
    | exact resolve eq38235 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845 eq38235
  have eq102963 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38597 eq3970
    | exact resolve eq3970 eq38597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3970 eq38597
  have eq103203 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13454 eq102963
    | exact resolve eq102963 eq13454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13454 eq102963
  have eq103383 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq103203
  have eq103392 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq103383
    | exact resolve eq103383 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103383
  have eq103398 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq103392 eq245
    | exact resolve eq245 eq103392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103405 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq103392 eq12929
    | exact resolve eq12929 eq103392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12929
  have eq103478 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq103392
  have eq103578 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq103405
  have eq103605 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12909 eq103398
    | exact resolve eq103398 eq12909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103398
  have eq103730 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq103605
  have eq103743 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq103730
       have r₂ := eq12930
       grind)
    | exact resolve eq103730 eq12930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103730
  have eq103748 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12909 eq103478
    | exact resolve eq103478 eq12909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12909 eq103478
  have eq103793 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq103748
  have eq103798 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq103793
       have r₂ := eq12930
       grind)
    | exact resolve eq103793 eq12930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103793
  have eq104428 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103798 eq120
    | exact resolve eq120 eq103798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103798
  have eq104587 : y = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq104428
    | exact resolve eq104428 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104428
  have eq104641 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq104587
       grind)
    | exact superpose eq104587 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq104587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104587
  have eq104642 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq104641
  have eq104754 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op y y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3919 y x y
       have i₂ := eq104642
       grind)
    | exact superpose eq104642 eq3919
    | exact resolve eq3919 eq104642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq139050 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq104754 X0
       have i₂ := eq104642
       grind)
    | exact superpose eq104642 eq104754
    | exact resolve eq104754 eq104642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104642 eq104754
  have eq139136 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq139050 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139050
  have eq170887 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6950 X0 X1 (M.op X0 X1)
       have i₂ := eq430 X1 X0 X0 (M.op X0 X1)
       grind)
    | exact superpose eq430 eq6950
    | exact resolve eq6950 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq6950
  have eq1858414 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq19603 eq19928
    | exact resolve eq19928 eq19603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19603
  have eq1861317 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq27 eq1858414
    | exact resolve eq1858414 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858414
  have eq1861717 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq1861317
  have eq1862617 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq18971 eq1861717
    | exact resolve eq1861717 eq18971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18971 eq1861717
  have eq1863169 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq1862617
  have eq1865518 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq1863169 eq120
    | exact resolve eq120 eq1863169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1863169
  have eq1866294 : y = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq30 eq1865518
    | exact resolve eq1865518 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1865518
  have eq1866522 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1866294
       grind)
    | exact superpose eq1866294 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq1866294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866294
  have eq1866637 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq1866522
  have eq2063097 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq103578 eq25713
    | exact resolve eq25713 eq103578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25713 eq103578
  have eq2066317 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2063097 eq7016
    | exact resolve eq7016 eq2063097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7016 eq2063097
  have eq2066644 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2066317
       have r₂ := eq12930
       grind)
    | exact resolve eq2066317 eq12930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12930 eq2066317
  have eq2066671 : (σ y) = (k (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2066644
       have r₂ := eq103743
       grind)
    | exact resolve eq2066644 eq103743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066644
  have eq2068673 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103743 eq2066671
    | exact resolve eq2066671 eq103743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103743 eq2066671
  have eq2068796 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2068673
  have eq2068838 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2068796 eq70
    | exact resolve eq70 eq2068796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068796
  have eq2068933 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2068838
  have eq2068950 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2068933
       have r₂ := eq12914
       grind)
    | exact resolve eq2068933 eq12914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12914 eq2068933
  have eq2071412 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq139136 y
       have i₂ := eq2068950
       grind)
    | exact superpose eq2068950 eq139136
    | exact resolve eq139136 eq2068950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139136 eq2068950
  have eq2071638 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2071412
  have eq2071721 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2071638
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2071638
    | exact resolve eq2071638 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071638
  have eq2071722 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2071721
  have eq2071780 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2071722 eq28
    | exact resolve eq28 eq2071722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2071792 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2071722 eq3422
    | exact resolve eq3422 eq2071722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq2073754 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq2071792
    | exact resolve eq2071792 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071792
  have eq2076078 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2073754 eq245
    | exact resolve eq245 eq2073754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq2076457 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  have eq2076463 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2073754 eq250
    | exact resolve eq250 eq2073754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq2073754
  have eq2076934 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2071722 eq2076078
    | exact resolve eq2076078 eq2071722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076078
  have eq2077379 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2076934
  have eq2077422 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2071722 eq2076457
    | exact resolve eq2076457 eq2071722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076457
  have eq2078058 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2077422
  have eq2081078 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2071722 eq2076463
    | exact resolve eq2076463 eq2071722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071722 eq2076463
  have eq2081666 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2081078
  have eq2083021 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2077379 eq52
    | exact resolve eq52 eq2077379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077379
  have eq2083265 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2078058 eq70
    | exact resolve eq70 eq2078058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq2078058
  have eq2083351 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq2083265
  have eq2083364 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2083351
       have r₂ := eq2071780
       grind)
    | exact resolve eq2083351 eq2071780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083351
  have eq2084856 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2083021 eq185
    | exact resolve eq185 eq2083021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq2083021
  have eq2085829 : x = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2084856
    | exact resolve eq2084856 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2084856
  have eq2090544 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1866637
       have i₂ := eq2083364
       grind)
    | exact superpose eq2083364 eq1866637
    | exact resolve eq1866637 eq2083364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866637
  have eq2090639 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq2083364
       grind)
    | exact superpose eq2083364 eq50
    | exact resolve eq50 eq2083364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq2090732 : x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19928 y y
       have i₂ := eq2083364
       grind)
    | exact superpose eq2083364 eq19928
    | exact resolve eq19928 eq2083364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083364
  have eq2090815 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2090544
  have eq2090850 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2090732
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2090732
    | exact resolve eq2090732 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090732
  have eq2090891 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2090815
       have r₂ := eq2071780
       grind)
    | exact resolve eq2090815 eq2071780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090815
  have eq2091104 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2090850 eq3622
    | exact resolve eq3622 eq2090850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090850
  have eq2113056 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq170887 y x
       have i₂ := eq2090639
       grind)
    | exact superpose eq2090639 eq170887
    | exact resolve eq170887 eq2090639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170887 eq2090639
  have eq2114666 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2113056
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2113056
    | exact resolve eq2113056 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113056
  have eq2114714 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq2114666
       grind)
    | exact superpose eq2114666 eq121
    | exact resolve eq121 eq2114666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2115053 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2114714
  have eq2115133 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq2115053
    | exact resolve eq2115053 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115053
  have eq2127732 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3790 x
       have i₂ := eq2091104
       grind)
    | exact superpose eq2091104 eq3790
    | exact resolve eq3790 eq2091104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091104
  have eq2127940 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2127732
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq2127732
    | exact resolve eq2127732 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127732
  have eq2145770 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2127940 eq19928
    | exact resolve eq19928 eq2127940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127940
  have eq2154886 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2090891 eq2145770
    | exact resolve eq2145770 eq2090891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2145770
  have eq2155121 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq2154886
  have eq2155173 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2155121
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2155121
    | exact resolve eq2155121 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155121
  have eq2155221 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq244
       have i₂ := eq2155173
       grind)
    | exact superpose eq2155173 eq244
    | exact resolve eq244 eq2155173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155173
  have eq2156000 : y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2090891 eq2155221
    | exact resolve eq2155221 eq2090891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090891 eq2155221
  have eq2156211 : y = (M.op y y) ∨ x = y := by grind
  clear eq2156000
  have eq2298290 : x ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6654 y y
       have i₂ := eq2085829
       grind)
    | exact superpose eq2085829 eq6654
    | (have j0 := eq6654 y y
       grind)
    | exact resolve eq6654 eq2085829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6654 eq2085829
  have eq2298374 : x ≠ y ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2298290
  have eq2298601 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2298374
       have r₂ := eq2156211
       grind)
    | exact resolve eq2298374 eq2156211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298374
  have eq2303464 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2114666
       have i₂ := eq2298601
       grind)
    | exact superpose eq2298601 eq2114666
    | exact resolve eq2114666 eq2298601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114666 eq2298601
  have eq2303765 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2303464
  have eq2305927 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2303765 eq2081666
    | exact resolve eq2081666 eq2303765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081666
  have eq2305950 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2303765 eq2115133
    | exact resolve eq2115133 eq2303765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115133 eq2303765
  have eq2306028 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2305950
  have eq2306039 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2305927
  have eq2315830 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2306039 eq2306028
    | exact resolve eq2306028 eq2306039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306028 eq2306039
  have eq2316049 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq2315830
  have eq2316087 : y = (M.op x y) := by
    first
    | (have r₁ := eq2316049
       have r₂ := eq2071780
       grind)
    | exact resolve eq2316049 eq2071780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071780 eq2316049
  have eq2316100 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2316087 eq21
    | exact resolve eq21 eq2316087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2316272 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq2316087 eq3622
    | exact resolve eq3622 eq2316087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq2316289 : y = (M.op x (M.op y y)) := by
    first
    | exact superpose eq2316087 eq4138
    | exact resolve eq4138 eq2316087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4138
  have eq2316702 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2316100
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2316100
    | exact resolve eq2316100 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316100
  have eq2316716 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2316702 eq27
    | exact resolve eq27 eq2316702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2319233 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq3790 x
       have i₂ := eq2316272
       grind)
    | exact superpose eq2316272 eq3790
    | exact resolve eq3790 eq2316272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790 eq2316272
  have eq2319475 : (M.op (M.op x x) (M.op x x)) = (M.op y (M.op x x)) := by
    first
    | exact superpose eq2316087 eq2319233
    | exact resolve eq2319233 eq2316087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319233
  have eq2319500 : x = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq2319475
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq2319475
    | exact resolve eq2319475 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2319475
  have eq2319634 : y ≠ (M.op y y) ∨ x = (M.op (M.op y y) (M.op y y)) ∨ (M.op (M.op y y) (M.op y y)) = (k x (M.op y y)) := by
    first
    | (have i₁ := eq12 x (M.op y y)
       have i₂ := eq2316289
       grind)
    | exact superpose eq2316289 eq12
    | (have j0 := eq12 x (M.op y y)
       grind)
    | exact resolve eq12 eq2316289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316289
  have eq2319786 : x = (M.op (M.op x y) (M.op y y)) ∨ y ≠ (M.op y y) ∨ (M.op (M.op y y) (M.op y y)) = (k x (M.op y y)) := by
    first
    | (have i₁ := eq2319634
       have i₂ := eq20538 y
       grind)
    | exact superpose eq20538 eq2319634
    | exact resolve eq2319634 eq20538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319634
  have eq2319828 : x = y ∨ y ≠ (M.op y y) ∨ (M.op (M.op y y) (M.op y y)) = (k x (M.op y y)) := by
    first
    | exact superpose eq244 eq2319786
    | exact resolve eq2319786 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319786
  have eq2319848 : x = y ∨ (M.op (M.op y y) (M.op y y)) = (k x (M.op y y)) := by
    first
    | (have r₁ := eq2319828
       have r₂ := eq2156211
       grind)
    | exact resolve eq2319828 eq2156211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156211 eq2319828
  have eq2319860 : (M.op (M.op x y) (M.op y y)) = (k x (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq2319848
       have i₂ := eq20538 y
       grind)
    | exact superpose eq20538 eq2319848
    | exact resolve eq2319848 eq20538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20538 eq2319848
  have eq2319868 : y = (k x (M.op y y)) ∨ x = y := by
    first
    | exact superpose eq244 eq2319860
    | exact resolve eq2319860 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq2319860
  have eq2320990 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq19928 y (M.op x x)
       have i₂ := eq2319500
       grind)
    | exact superpose eq2319500 eq19928
    | exact resolve eq19928 eq2319500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19928 eq2319500
  have eq2321035 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2320990
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2320990
    | exact resolve eq2320990 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2320990
  have eq2321111 : y = (M.op y y) := by
    first
    | exact superpose eq2316087 eq2321035
    | exact resolve eq2321035 eq2316087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316087 eq2321035
  have eq2321352 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7512 y
       have i₂ := eq2321111
       grind)
    | exact superpose eq2321111 eq7512
    | exact resolve eq7512 eq2321111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7512
  have eq2321454 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2321352
  have eq2321519 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2321454
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2321454
    | exact resolve eq2321454 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321454
  have eq2321583 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2316702 eq2321519
    | exact resolve eq2321519 eq2316702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321519
  have eq2365857 : y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq2319868
       have i₂ := eq2321111
       grind)
    | exact superpose eq2321111 eq2319868
    | exact resolve eq2319868 eq2321111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319868 eq2321111
  have eq2365904 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5013 y
       have i₂ := eq2365857
       grind)
    | exact superpose eq2365857 eq5013
    | (have j0 := eq5013 y
       grind)
    | exact resolve eq5013 eq2365857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5013 eq2365857
  have eq2366001 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq2365904
  have eq2366103 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2366001
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2366001
    | exact resolve eq2366001 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366001
  have eq2366210 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq2366103
    | exact resolve eq2366103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2366103
  have eq2366314 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2316702 eq2366210
    | exact resolve eq2366210 eq2316702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366210
  have eq2366415 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq2366314
       have r₂ := eq28
       grind)
    | exact resolve eq2366314 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366314
  have eq2366500 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2366415
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2366415
    | exact resolve eq2366415 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366415
  have eq2366575 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2316702 eq2366500
    | exact resolve eq2366500 eq2316702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366500
  have eq2366648 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq2321583 eq2366575
    | exact resolve eq2366575 eq2321583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366575
  have eq2367769 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2366648 eq2316716
    | exact resolve eq2316716 eq2366648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366648
  have eq2367790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2321583 eq2367769
    | exact resolve eq2367769 eq2321583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367769
  have eq2367952 : x = y := by
    first
    | (have r₁ := eq2367790
       have r₂ := eq28
       grind)
    | exact resolve eq2367790 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367790
  have eq2368273 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2367952
       grind)
    | exact superpose eq2367952 eq25
    | exact resolve eq25 eq2367952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2367952
  have eq2370334 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2316702 eq2368273
    | exact resolve eq2368273 eq2316702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316702 eq2368273
  have eq2371018 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2370334
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2370334
    | exact resolve eq2370334 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2370334
  have eq2372692 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2371018 eq2316716
    | exact resolve eq2316716 eq2371018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316716 eq2371018
  have eq2372710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2321583 eq2372692
    | exact resolve eq2372692 eq2321583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321583 eq2372692
  have eq2372875 : False := by grind
  exact eq2372875

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_y_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
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
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq186 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq186
    | (have j0 := eq186 y x
       grind)
    | exact resolve eq186 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq186
    | (have j0 := eq186 (σ y) (σ x)
       grind)
    | exact resolve eq186 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq174 (M.op X0 X0)
       have i₂ := eq186 X0 X0
       grind)
    | exact superpose eq186 eq174
    | exact resolve eq174 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X2
       have i₂ := eq186 X0 X0
       grind)
    | exact superpose eq186 eq16
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq202 eq16
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq203 eq16
    | exact resolve eq16 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq141
    | exact resolve eq141 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq174
  have eq269 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq248
    | exact resolve eq248 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq344 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq207 sF2
       grind)
    | exact superpose eq207 eq90
    | exact resolve eq90 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq345 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq207 sF3
       grind)
    | exact superpose eq207 eq107
    | exact resolve eq107 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq207
  have eq439 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ y))) = (σ (k X0 (k y y))) := by
    intro X0
    first
    | exact superpose eq115 eq38
    | exact resolve eq38 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq115
  have eq649 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq651 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq696 (M.op X0 X0)
       have i₂ := eq186 X0 X0
       grind)
    | exact superpose eq186 eq696
    | (have j0 := eq696 X0
       grind)
    | exact resolve eq696 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq909 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq696 X0
       grind)
    | exact superpose eq696 eq186
    | (have j1 := eq696 X0
       grind)
    | exact resolve eq186 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq186 X0 X0
       have i₂ := eq696 X0
       grind)
    | exact superpose eq696 eq186
    | (have j1 := eq696 X0
       grind)
    | exact resolve eq186 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq696 eq903
    | (have j0 := eq903 X0
       have j1 := eq696 X0
       grind)
    | exact resolve eq903 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq1118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq649
       grind)
    | exact superpose eq649 eq39
    | exact resolve eq39 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1118
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1118
    | exact resolve eq1118 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1119
    | exact resolve eq1119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq2665 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1 (M.op X0 X0)
       have i₂ := eq186 X0 X0
       grind)
    | exact superpose eq186 eq208
    | exact resolve eq208 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2667 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq213 eq208
    | exact resolve eq208 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2668 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq175 eq208
    | exact resolve eq208 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2669 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq216 eq208
    | exact resolve eq208 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq2718 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2665 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2665
    | (have j0 := eq2665 y x
       grind)
    | exact resolve eq2665 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2753 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq202
       have i₂ := eq2718
       grind)
    | exact superpose eq2718 eq202
    | exact resolve eq202 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq2761 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq186 y X0
       have i₂ := eq2718
       grind)
    | exact superpose eq2718 eq186
    | exact resolve eq186 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2765 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (M.op X0 (M.op (M.op (M.op x y) y) X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq208 y X1 x
       have i₂ := eq2718
       grind)
    | exact superpose eq2718 eq208
    | exact resolve eq208 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2769 : (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ (k y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq2718
       grind)
    | exact superpose eq2718 eq12
    | exact resolve eq12 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2772 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq2769
  have eq2786 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2753 eq16
    | exact resolve eq16 eq2753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2753
  have eq2861 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) x) := by
    intro X0
    first
    | exact superpose eq2668 eq208
    | exact resolve eq208 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2882 : (M.op y y) = (M.op (k (M.op x y) (M.op x y)) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2667 sF0
       have i₂ := eq696 sF0
       grind)
    | exact superpose eq696 eq2667
    | (have j1 := eq696 (M.op x y)
       grind)
    | exact resolve eq2667 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2890 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2667 eq208
    | exact resolve eq208 eq2667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq2898 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op (M.op x y) y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2890 X0
       have i₂ := eq2718
       grind)
    | exact superpose eq2718 eq2890
    | exact resolve eq2890 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq2901 : (M.op (M.op x y) y) = (M.op (k (M.op x y) (M.op x y)) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2882
       have i₂ := eq2718
       grind)
    | exact superpose eq2718 eq2882
    | exact resolve eq2882 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882
  have eq2912 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2669 eq208
    | exact resolve eq208 eq2669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3041 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2786 eq2861
    | exact resolve eq2861 eq2786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786 eq2861
  have eq3065 : ∀ X0 : G, (M.op (M.op x y) x) ≠ X0 ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) x) x
       have r₂ := eq3041
       grind)
    | exact resolve eq13 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3066 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op x X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq16
    | exact resolve eq16 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3068 : x = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq178
    | exact resolve eq178 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3069 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq186 x X0
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq186
    | exact resolve eq186 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq3077 : (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ (k x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq12
    | exact resolve eq12 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3080 : (k x x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq3077
  have eq3656 : ∀ X0 : G, (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq2898 eq208
    | exact resolve eq208 eq2898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq2898
  have eq3667 : ∀ X0 : G, y = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq2761 eq3656
    | exact resolve eq3656 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3656
  have eq3700 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq203 eq2912
    | exact resolve eq2912 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq2912
  have eq13312 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq213 eq2765
    | exact resolve eq2765 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq2765
  have eq24192 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq909 X0 X0
       have i₂ := eq696 X0
       grind)
    | exact superpose eq696 eq909
    | (have j0 := eq909 X0 x
       have j1 := eq696 X0
       grind)
    | exact resolve eq909 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq909
  have eq24529 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq24192 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq24192 X0
       have r₂ := eq13 X0 (k X0 X0)
       grind)
    | (have r₁ := eq24192 (M.op x x)
       have r₂ := eq13 (M.op (k (M.op x x) (M.op x x)) (k (M.op x x) (M.op x x))) x
       grind)
    | (have r₁ := eq24192 (M.op x x)
       have r₂ := eq13 (k (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq24192 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24192
  have eq24795 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (k (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (k X0 X0) (k X0 X0)
       have i₂ := eq913 X0
       grind)
    | exact superpose eq913 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq913 X0
       grind)
    | exact resolve eq12 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq24814 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq24795 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24795
  have eq24826 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq24814 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq24814 (M.op x x)
       have r₂ := eq13 (k (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq24814 (M.op x x)
       have r₂ := eq13 (k (k (M.op x x) (M.op x x)) (k (M.op x x) (M.op x x))) x
       grind)
    | (have r₁ := eq24814 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq24814 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24814
  have eq25345 : (σ y) = (k (σ (k y y)) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq439 (k y y)
       have i₂ := eq970 y
       grind)
    | exact superpose eq970 eq439
    | (have j1 := eq970 y
       grind)
    | exact resolve eq439 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq25359 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq25345
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq25345
    | exact resolve eq25345 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25345
  have eq25373 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq25359
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25359
    | exact resolve eq25359 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25359
  have eq25381 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq25373
       have i₂ := eq2718
       grind)
    | exact superpose eq2718 eq25373
    | exact resolve eq25373 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718 eq25373
  have eq30690 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 (k X0 X0)
       have i₂ := eq24529 X0
       grind)
    | exact superpose eq24529 eq178
    | (have j1 := eq24529 X0
       grind)
    | exact resolve eq178 eq24529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24529
  have eq36762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1121 eq651
    | exact resolve eq651 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq1121
  have eq36771 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq36762
       have r₂ := eq27
       grind)
    | exact resolve eq36762 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36762
  have eq36778 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36771
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq36771
    | exact resolve eq36771 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36771
  have eq36783 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq36778
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq36778
    | exact resolve eq36778 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36778
  have eq36812 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq36783 eq178
    | exact resolve eq178 eq36783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36783
  have eq37044 : x = (k (τ (σ y)) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq36812 eq269
    | exact resolve eq269 eq36812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq36812
  have eq37116 : x = (k y x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31 eq37044
    | exact resolve eq37044 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37044
  have eq37128 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k y x) := by
    first
    | (have j1 := eq3065 y
       grind)
    | (have r₁ := eq37116
       have r₂ := eq3065 (M.op x y)
       grind)
    | (have r₁ := eq37116
       have r₂ := eq3065 y
       grind)
    | exact resolve eq37116 eq3065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065 eq37116
  have eq37138 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k y x) := by
    first
    | exact superpose eq37128 eq2669
    | exact resolve eq2669 eq37128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2669
  have eq37178 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k y x) := by
    first
    | exact superpose eq37128 eq2665
    | exact resolve eq2665 eq37128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37193 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k y x) := by
    first
    | exact superpose eq3700 eq37178
    | exact resolve eq37178 eq3700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3700 eq37178
  have eq37201 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k y x) := by
    first
    | exact superpose eq26 eq37138
    | exact resolve eq37138 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37138
  have eq37205 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k y x) := by
    first
    | exact superpose eq37128 eq37193
    | exact resolve eq37193 eq37128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37128 eq37193
  have eq37243 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (k y x) := by
    first
    | exact superpose eq37201 eq178
    | exact resolve eq178 eq37201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq37201
  have eq37289 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq37205 eq37243
    | exact resolve eq37243 eq37205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37205 eq37243
  have eq37326 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op x X1)) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    intro X0 X1
    first
    | exact superpose eq37289 eq3066
    | exact resolve eq3066 eq37289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3066
  have eq37334 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq37289 eq3080
    | exact resolve eq3080 eq37289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080
  have eq37340 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq37289 eq3069
    | exact resolve eq3069 eq37289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3069 eq37289
  have eq39102 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq24826 x
       have i₂ := eq37334
       grind)
    | exact superpose eq37334 eq24826
    | exact resolve eq24826 eq37334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24826 eq37334
  have eq39113 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq39102
  have eq39134 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq39113 eq2901
    | exact resolve eq2901 eq39113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2901
  have eq39143 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq39113 eq41
    | exact resolve eq41 eq39113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq39175 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq39143
    | exact resolve eq39143 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39143
  have eq39179 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq39134
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39134
    | exact resolve eq39134 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39134
  have eq39183 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq39175
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39175
    | exact resolve eq39175 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39175
  have eq39185 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq37340 eq39179
    | exact resolve eq39179 eq37340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39179
  have eq39186 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq39185
  have eq39928 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq37326 eq13312
    | exact resolve eq13312 eq37326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37326
  have eq39978 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq39928
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39928
    | exact resolve eq39928 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39928
  have eq40041 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq39978 eq2772
    | exact resolve eq2772 eq39978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40054 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq39978 eq2761
    | exact resolve eq2761 eq39978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761 eq39978
  have eq40105 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq37340 eq40054
    | exact resolve eq40054 eq37340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37340 eq40054
  have eq40904 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq40041
       grind)
    | exact superpose eq40041 eq40
    | exact resolve eq40 eq40041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40041
  have eq40941 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq40904
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40904
    | exact resolve eq40904 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40904
  have eq40960 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq40941
    | exact resolve eq40941 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40941
  have eq40972 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq40105 eq40960
    | exact resolve eq40960 eq40105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40105 eq40960
  have eq40983 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq40972 eq25381
    | exact resolve eq25381 eq40972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25381
  have eq40999 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq40972 eq970
    | (have j0 := eq970 (σ y)
       grind)
    | exact resolve eq970 eq40972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq40972
  have eq41009 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq39183 eq40999
    | exact resolve eq40999 eq39183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40999
  have eq41010 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq41009
  have eq41016 : (σ x) = (σ y) ∨ y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq39183 eq40983
    | exact resolve eq40983 eq39183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39183 eq40983
  have eq41017 : (σ x) = (σ y) ∨ y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq41016
  have eq41025 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39186 eq41017
    | exact resolve eq41017 eq39186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39186 eq41017
  have eq41151 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq41010 eq345
    | exact resolve eq345 eq41010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq41010
  have eq41233 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq31 eq41151
    | exact resolve eq41151 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41151
  have eq41239 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq41025 eq41233
    | exact resolve eq41233 eq41025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41025 eq41233
  have eq41297 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq41239 eq39113
    | exact resolve eq39113 eq41239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39113 eq41239
  have eq41315 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq41297
  have eq41325 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq649
       have i₂ := eq41315
       grind)
    | exact superpose eq41315 eq649
    | exact resolve eq649 eq41315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq41315
  have eq41329 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq41325
  have eq41333 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41329
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq41329
    | exact resolve eq41329 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41329
  have eq41338 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41333
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq41333
    | exact resolve eq41333 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041 eq41333
  have eq41447 : y = (M.op (M.op x y) x) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41338 eq3068
    | exact resolve eq3068 eq41338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41338
  have eq41651 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41447 eq3068
    | exact resolve eq3068 eq41447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068 eq41447
  have eq41720 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41651
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41651
    | exact resolve eq41651 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41651
  have eq41721 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq41720
  have eq41758 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41721 eq13312
    | exact resolve eq13312 eq41721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13312
  have eq41783 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41721 eq2665
    | exact resolve eq2665 eq41721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq41799 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41721 eq41783
    | exact resolve eq41783 eq41721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41721 eq41783
  have eq41802 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41758
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41758
    | exact resolve eq41758 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41758
  have eq41821 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op (M.op x y) y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq41799 eq3667
    | exact resolve eq3667 eq41799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667
  have eq41915 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq41802 eq41821
    | exact resolve eq41821 eq41802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41802 eq41821
  have eq41922 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2668 eq41915
    | exact resolve eq41915 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668 eq41915
  have eq41924 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq41799 eq41922
    | exact resolve eq41922 eq41799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41799 eq41922
  have eq41926 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq41924 eq31
    | exact resolve eq31 eq41924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41924
  have eq42136 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq41926
    | exact resolve eq41926 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41926
  have eq42137 : x = (M.op x y) ∨ x = y := by grind
  clear eq42136
  have eq42153 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq42137
       grind)
    | exact superpose eq42137 eq18
    | exact resolve eq18 eq42137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42154 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq42137
       grind)
    | exact superpose eq42137 eq22
    | exact resolve eq22 eq42137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42273 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq42154
    | exact resolve eq42154 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42154
  have eq42410 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq42153 eq2772
    | exact resolve eq2772 eq42153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2772 eq42153
  have eq43905 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq42410
       grind)
    | exact superpose eq42410 eq40
    | exact resolve eq40 eq42410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq42410
  have eq43938 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq43905
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43905
    | exact resolve eq43905 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43905
  have eq43943 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq43938
    | exact resolve eq43938 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43938
  have eq43947 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq42273 eq43943
    | exact resolve eq43943 eq42273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43943
  have eq44068 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq43947 eq30690
    | exact resolve eq30690 eq43947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30690 eq43947
  have eq44075 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq44068
    | exact resolve eq44068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44068
  have eq44835 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq44075 eq27
    | exact resolve eq27 eq44075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44075
  have eq45020 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq44835
       have r₂ := eq42273
       grind)
    | exact resolve eq44835 eq42273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42273 eq44835
  have eq46753 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq45020 eq31
    | exact resolve eq31 eq45020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq45020
  have eq46981 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq46753
    | exact resolve eq46753 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46753
  have eq46982 : y = (M.op x y) ∨ x = y := by grind
  clear eq46981
  have eq47182 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq46982
  have eq47186 : x = y := by
    first
    | (have r₁ := eq47182
       have r₂ := eq42137
       grind)
    | exact resolve eq47182 eq42137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42137 eq47182
  have eq47232 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq47186
       grind)
    | exact superpose eq47186 eq18
    | exact resolve eq18 eq47186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq47233 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq47186
       grind)
    | exact superpose eq47186 eq24
    | exact resolve eq24 eq47186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq47186
  have eq47394 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq47233
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47233
    | exact resolve eq47233 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47233
  have eq47398 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq47394 eq26
    | exact resolve eq26 eq47394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq47394
  have eq47672 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq47232
       grind)
    | exact superpose eq47232 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq47232
       grind)
    | exact resolve eq13 eq47232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47688 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq47232
       grind)
    | exact superpose eq47232 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq47232
       grind)
    | exact resolve eq12 eq47232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47232
  have eq47711 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq47688
  have eq47749 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq47398 eq344
    | exact resolve eq344 eq47398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq47785 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq47398 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq47398
       grind)
    | exact resolve eq12 eq47398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47398
  have eq47808 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq47785
  have eq52140 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq47711
       grind)
    | exact superpose eq47711 eq39
    | exact resolve eq39 eq47711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52170 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52140
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52140
    | exact resolve eq52140 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52140
  have eq52176 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq52170
    | exact resolve eq52170 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52170
  have eq52318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52176 eq47808
    | exact resolve eq47808 eq52176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52176
  have eq52349 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq52318
       have r₂ := eq27
       grind)
    | exact resolve eq52318 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52318
  have eq52486 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52349 eq47749
    | exact resolve eq47749 eq52349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47749 eq52349
  have eq52504 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq52486
    | exact resolve eq52486 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52486
  have eq52581 : x = (k x x) := by
    first
    | (have j1 := eq47672 x
       grind)
    | (have r₁ := eq52504
       have r₂ := eq47672 x
       grind)
    | exact resolve eq52504 eq47672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47672 eq52504
  have eq52639 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47711
       have i₂ := eq52581
       grind)
    | exact superpose eq52581 eq47711
    | exact resolve eq47711 eq52581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47711
  have eq52641 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq52581
       grind)
    | exact superpose eq52581 eq39
    | exact resolve eq39 eq52581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq52581
  have eq52657 : x = (M.op x y) := by grind
  clear eq52639
  have eq52674 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq52641
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52641
    | exact resolve eq52641 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52641
  have eq52690 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq52657
       grind)
    | exact superpose eq52657 eq22
    | exact resolve eq22 eq52657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq52657
  have eq52858 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq52690 eq20
    | exact resolve eq20 eq52690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq52690
  have eq53589 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52674 eq47808
    | exact resolve eq47808 eq52674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47808 eq52674
  have eq53608 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq53589
  have eq53617 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq53608 eq27
    | exact resolve eq27 eq53608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq53608
  have eq53825 : False := by grind
  exact eq53825

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_y_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq57
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq57
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq264 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq76
  have eq267 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq264 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq264
    | exact resolve eq264 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq274 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq267 (σ X0)
       grind)
    | exact superpose eq267 eq31
    | exact resolve eq31 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq276 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq267 (τ X0)
       grind)
    | exact superpose eq267 eq18
    | exact resolve eq18 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq276
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq280 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq274 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq274
    | exact resolve eq274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq300 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq278 (τ X0)
       grind)
    | exact superpose eq278 eq18
    | exact resolve eq18 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq305 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq300
    | exact resolve eq300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq375 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq62 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq376 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq380 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq376 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq376
    | (have j0 := eq376 X0
       grind)
    | exact resolve eq376 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq778 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq106 X0 X1 X2
       grind)
    | exact superpose eq106 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq106 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq106 X0 X1 X2
       grind)
    | exact resolve eq13 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq778 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq788 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq787 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq789 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k X2 (k (τ X0) X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq788 X0 X1 X2
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq788
    | (have j0 := eq788 X0 X1 X2
       grind)
    | exact resolve eq788 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq788
  have eq825 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (k (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k (σ X0) X1)
       have i₂ := eq107 X0 X1 X2
       grind)
    | exact superpose eq107 eq13
    | (have j0 := eq13 (σ X2) (k (σ X0) X1)
       have j1 := eq107 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq107 X0 X1 X2
       grind)
    | exact resolve eq13 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (k (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq825 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq835 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (k (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq834 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq836 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k X2 (k X0 (τ X1)))) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq835 X0 X1 X2
       have i₂ := eq29 X0 X1 X2
       grind)
    | exact superpose eq29 eq835
    | (have j0 := eq835 X0 X1 X2
       grind)
    | exact resolve eq835 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq835
  have eq2160 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq34
    | (have j1 := eq380 X0
       grind)
    | exact resolve eq34 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq380
  have eq2188 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2160 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2160
    | (have j0 := eq2160 X0
       grind)
    | exact resolve eq2160 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2189 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2188 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188
  have eq2194 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2189 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2189
    | exact resolve eq2189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189
  have eq2245 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2194 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2194
    | exact resolve eq2194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq2316 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq2245 X0
       grind)
    | exact superpose eq2245 eq10
    | exact resolve eq10 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2369 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2316 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2316
    | exact resolve eq2316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316
  have eq2464 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2369 (σ X0)
       grind)
    | exact superpose eq2369 eq15
    | exact resolve eq15 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369
  have eq2486 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2464 X0
       have i₂ := eq2245 X0
       grind)
    | exact superpose eq2245 eq2464
    | exact resolve eq2464 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245 eq2464
  have eq3502 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq2486 X0
       grind)
    | exact superpose eq2486 eq25
    | exact resolve eq25 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28419 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) ≠ (M.op (k X1 (σ X2)) (σ X0)) ∨ (σ X0) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (k X1 (σ X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq789 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq28420 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (k X1 (σ X2)) (σ X0)) ∨ (σ X0) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28419 X0 X1 X2
       have j1 := eq106 X1 X2 X0
       grind)
    | (have r₁ := eq28419 X2 X0 X1
       have r₂ := eq106 X0 X1 X2
       grind)
    | exact resolve eq28419 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq28419
  have eq28941 : ∀ X0 X1 X2 : G, (k (σ X1) X2) ≠ (M.op (k (σ X1) X2) (σ X0)) ∨ (σ X0) = (M.op (k (σ X1) X2) (k (σ X1) X2)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (k (σ X1) X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq836 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq28942 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (k (σ X1) X2) (σ X0)) ∨ (σ X0) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28941 X0 X1 X2
       have j1 := eq107 X1 X2 X0
       grind)
    | (have r₁ := eq28941 X2 X0 X1
       have r₂ := eq107 X0 X1 X2
       grind)
    | exact resolve eq28941 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq28941
  have eq560459 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) (σ X1)) ∨ (σ X1) = (M.op (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq28420 X1 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq278 (τ X0)
       grind)
    | exact superpose eq278 eq28420
    | (have j0 := eq28420 X1 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       grind)
    | exact resolve eq28420 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq28420
  have eq561125 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq560459 X0 X1
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq560459
    | (have j0 := eq560459 X0 X1
       grind)
    | exact resolve eq560459 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560459
  have eq561264 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq561125 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq561125
    | (have j0 := eq561125 X0 X1
       grind)
    | exact resolve eq561125 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq561125
  have eq561352 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq561264 X0 X1
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq561264
    | (have j0 := eq561264 X0 X1
       grind)
    | exact resolve eq561264 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq561264
  have eq561514 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq561352 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq561352
    | exact resolve eq561352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561352
  have eq562306 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (k (σ X0) (M.op (σ X0) (σ X0))) (σ X1)) ∨ (σ X1) = (M.op (k (σ X0) (M.op (σ X0) (σ X0))) (k (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28942 X1 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq28942
    | (have j0 := eq28942 X1 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq28942 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq28942
  have eq563020 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (k (σ X0) (M.op (σ X0) (σ X0))) (k (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq562306 X0 X1
       have i₂ := eq267 (σ X0)
       grind)
    | exact superpose eq267 eq562306
    | (have j0 := eq562306 X0 X1
       grind)
    | exact resolve eq562306 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562306
  have eq563156 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq563020 X0 X1
       have i₂ := eq267 (σ X0)
       grind)
    | exact superpose eq267 eq563020
    | (have j0 := eq563020 X0 X1
       grind)
    | exact resolve eq563020 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq563020
  have eq563247 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq563156 X0 X1
       have i₂ := eq2486 X0
       grind)
    | exact superpose eq2486 eq563156
    | (have j0 := eq563156 X0 X1
       grind)
    | exact resolve eq563156 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486 eq563156
  have eq594492 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq563247 x y
       grind)
    | exact superpose eq563247 eq16
    | (have j1 := eq563247 x y
       grind)
    | exact resolve eq16 eq563247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563247
  have eq595757 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq594492
       have i₂ := eq561514 y x
       grind)
    | exact superpose eq561514 eq594492
    | (have j1 := eq561514 y x
       grind)
    | exact resolve eq594492 eq561514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561514 eq594492
  have eq595784 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq595757
  have eq599210 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq595784
       grind)
    | exact superpose eq595784 eq10
    | exact resolve eq10 eq595784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595784
  have eq599626 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq599210
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq599210
    | exact resolve eq599210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599210
  have eq599627 : y = (M.op x x) := by grind
  clear eq599626
  have eq599683 : x = (M.op x y) := by
    first
    | (have i₁ := eq25 x
       have i₂ := eq599627
       grind)
    | exact superpose eq599627 eq25
    | exact resolve eq25 eq599627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq599697 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3502 x
       have i₂ := eq599627
       grind)
    | exact superpose eq599627 eq3502
    | exact resolve eq3502 eq599627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3502 eq599627
  have eq664148 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq599697
       grind)
    | exact superpose eq599697 eq16
    | exact resolve eq16 eq599697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599697
  have eq664690 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq664148
       have i₂ := eq599683
       grind)
    | exact superpose eq599683 eq664148
    | exact resolve eq664148 eq599683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599683 eq664148
  have eq664691 : False := by grind
  exact eq664691

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxx_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (k (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq47 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq96 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (τ X0)
       have i₂ := eq53 (τ X0)
       grind)
    | exact superpose eq53 eq20
    | exact resolve eq20 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq97
    | exact resolve eq97 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq97
  have eq109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq26
    | exact resolve eq26 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op (k (M.op X0 X0) X0) (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    grind
  have eq215 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq25
    | exact resolve eq25 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    by_contra hcon
    push Not at hcon
    have f218_13 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
      intro X0 X1 X2 X3
      grind
    have f218_22 : (M.op X3 (M.op X0 (M.op X1 X2))) ≠ (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by grind
    have f218_102 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
      intro X0 X1 X2 X3 X4 X5
      first
      | (have i₁ := f218_13 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
         have i₂ := f218_13 X0 X1 X2 X3
         grind)
      | exact superpose f218_13 f218_13
      | exact resolve f218_13 f218_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f218_2403 : (M.op X3 (M.op X0 (M.op X1 X2))) ≠ (M.op X3 (M.op X0 (M.op X1 X2))) := by
      first
      | (have i₁ := f218_22
         have i₂ := f218_102 X0 X1 X2 X3 X4 X5
         grind)
      | exact superpose f218_102 f218_22
      | (have r₁ := f218_22
         have r₂ := f218_102 X0 X1 X2 X3 X4 X5
         grind)
      | exact resolve f218_22 f218_102
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f218_2435 : False := by grind
    exact f218_2435
  have eq232 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (k (M.op X1 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq25 X1 X1 X0 X2
       grind)
    | exact superpose eq25 eq52
    | exact resolve eq52 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq262 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq109 X1
       grind)
    | exact superpose eq109 eq67
    | (have j0 := eq67 X0 X1
       grind)
    | exact resolve eq67 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq275 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ (M.op X0 X0))
       have i₂ := eq150 X0
       grind)
    | exact superpose eq150 eq9
    | exact resolve eq9 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq275
    | exact resolve eq275 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq293 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq262 x y
       grind)
    | exact superpose eq262 eq16
    | (have j1 := eq262 x y
       grind)
    | exact resolve eq16 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq347 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 (σ (τ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq276 (τ X0) X1
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq276
    | exact resolve eq276 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq276
  have eq353 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq347 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq387 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq398 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq26 (M.op X0 X0)
       have i₂ := eq353 X0 X0
       grind)
    | exact superpose eq353 eq26
    | exact resolve eq26 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq150 (M.op X0 X0)
       have i₂ := eq353 X0 X0
       grind)
    | exact superpose eq353 eq150
    | exact resolve eq150 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq293
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq293
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq293
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq293
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq293 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq810 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq809
  have eq1028 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) (k (M.op X1 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq215 X1 X0 X1
       grind)
    | exact superpose eq215 eq52
    | exact resolve eq52 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1040 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1028 X0 X1 X2
       have i₂ := eq387 X1
       grind)
    | exact superpose eq387 eq1028
    | exact resolve eq1028 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1390 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq232 X0 X1 X2 X3
       have i₂ := eq387 X1
       grind)
    | exact superpose eq387 eq232
    | exact resolve eq232 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq1473 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1390 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq26 (M.op X0 X1)
       grind)
    | exact superpose eq26 eq1390
    | exact resolve eq1390 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1529 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1473 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq353 X0 X1
       grind)
    | exact superpose eq353 eq1473
    | exact resolve eq1473 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq1473
  have eq2431 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163 X0 X1 X2
       have i₂ := eq387 (M.op X0 X1)
       grind)
    | exact superpose eq387 eq163
    | exact resolve eq163 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq2562 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2431 (M.op X3 (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1390 X0 X1 X2 X3
       grind)
    | exact superpose eq1390 eq2431
    | exact resolve eq2431 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390 eq2431
  have eq2693 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X0 X0) X0) = (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4
    grind
  clear eq2562
  have eq2707 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2693 X0 X1 X2 X3 X4
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq2693
    | exact resolve eq2693 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2693
  have eq5029 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op (k (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X2) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207 X0 X1 X2
       have i₂ := eq1529 (M.op (M.op X0 X0) X2) X1
       grind)
    | exact superpose eq1529 eq207
    | exact resolve eq207 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq5030 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op (M.op X0 X0) X2) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5029 X0 X1 X2
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq5029
    | exact resolve eq5029 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq5029
  have eq5050 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5030 X0 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq215 X0 X1 X0
       grind)
    | exact superpose eq215 eq5030
    | exact resolve eq5030 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq5030
  have eq5232 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq218 X0 X1 X2 X3 X4 X5
       have i₂ := eq1529 (M.op X0 (M.op X1 X2)) X3
       grind)
    | exact superpose eq1529 eq218
    | exact resolve eq218 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq5437 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5232 (M.op X1 X2) X1 X2 (k (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X1 X2)) x x
       have i₂ := eq49 (M.op X1 X2)
       grind)
    | exact superpose eq49 eq5232
    | exact resolve eq5232 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq5232
  have eq5526 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5437 X0 X1 X2 X3
       have i₂ := eq398 (M.op X0 X1)
       grind)
    | exact superpose eq398 eq5437
    | exact resolve eq5437 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5437
  have eq5575 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5526 X0 X1 X2 X3
       have i₂ := eq1529 X1 X0
       grind)
    | exact superpose eq1529 eq5526
    | exact resolve eq5526 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529 eq5526
  have eq10895 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X4 (M.op X1 (M.op X2 X0)))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5575 (M.op X2 (M.op X0 X1)) X1 X2 X3
       have i₂ := eq1040 X0 X1 X2
       grind)
    | exact superpose eq1040 eq5575
    | exact resolve eq5575 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq5575
  have eq11235 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X4 (M.op X1 (M.op X2 X0)))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10895 X0 X1 X2 X3 X4
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10895
    | exact resolve eq10895 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10895
  have eq14733 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2))))) (M.op X2 X2)) = X2 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2707 X2 X4 X5 (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) X3
       have i₂ := eq5050 X1 X2 X0
       grind)
    | exact superpose eq5050 eq2707
    | exact resolve eq2707 eq5050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707 eq5050
  have eq20510 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq810
       grind)
    | exact superpose eq810 eq16
    | exact resolve eq16 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq20511 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20510
       have r₂ := eq109 x
       grind)
    | exact resolve eq20510 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20510
  have eq270366 : ∀ X0 X1 X2 X3 : G, y = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X3 x)))) x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14733 X0 y y X3 x x
       have i₂ := eq20511
       grind)
    | exact superpose eq20511 eq14733
    | exact resolve eq14733 eq20511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14733 eq20511
  have eq270411 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq270366 x x x x
       have i₂ := eq11235 x x x x x
       grind)
    | exact superpose eq11235 eq270366
    | exact resolve eq270366 eq11235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11235 eq270366
  have eq414820 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq270411
       grind)
    | exact superpose eq270411 eq10
    | exact resolve eq10 eq270411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270411
  have eq415154 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq414820
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq414820
    | exact resolve eq414820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414820
  have eq415157 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq415154
       grind)
    | exact superpose eq415154 eq16
    | exact resolve eq16 eq415154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415154
  have eq415158 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq415157
       have r₂ := eq109 x
       grind)
    | exact resolve eq415157 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq415157
  have eq415164 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq415158
       grind)
    | exact superpose eq415158 eq26
    | exact resolve eq26 eq415158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq415169 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq150 x
       have i₂ := eq415158
       grind)
    | exact superpose eq415158 eq150
    | exact resolve eq150 eq415158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq415158
  have eq463431 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq415169
       grind)
    | exact superpose eq415169 eq16
    | exact resolve eq16 eq415169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415169
  have eq463950 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq463431
       have i₂ := eq415164
       grind)
    | exact superpose eq415164 eq463431
    | exact resolve eq463431 eq415164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415164 eq463431
  have eq463981 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq463950
  have eq463982 : (σ x) = (σ (M.op y y)) := by grind
  clear eq463981
  have eq464061 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq403 y
       have i₂ := eq463982
       grind)
    | exact superpose eq463982 eq403
    | exact resolve eq403 eq463982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq464131 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq463982
       grind)
    | exact superpose eq463982 eq10
    | exact resolve eq10 eq463982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463982
  have eq464626 : x = (M.op y y) := by
    first
    | (have i₁ := eq464131
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq464131
    | exact resolve eq464131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464131
  have eq464882 : x = (M.op x y) := by
    first
    | (have i₁ := eq398 y
       have i₂ := eq464626
       grind)
    | exact superpose eq464626 eq398
    | exact resolve eq398 eq464626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq464626
  have eq502679 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq464061
       grind)
    | exact superpose eq464061 eq16
    | exact resolve eq16 eq464061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464061
  have eq503181 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq502679
       have i₂ := eq464882
       grind)
    | exact superpose eq464882 eq502679
    | exact resolve eq502679 eq464882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464882 eq502679
  have eq503182 : False := by grind
  exact eq503182
