import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3078`: `x = (((x ◇ y) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pxy_Equation3078 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3078 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3078.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X1) X0) = X0 := by
    intro X0 X1
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
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x = (M.op (M.op (M.op (M.op x y) y) y) x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 X0) X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq86 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq101
  have eq109 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq98
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq111
    | exact resolve eq111 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq209 : ∀ X0 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (τ X0) X1
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq76
    | (have j0 := eq76 X0
       grind)
    | exact resolve eq76 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq582 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq809 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq812 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ x)
       have i₂ := eq92 x x
       grind)
    | exact superpose eq92 eq56
    | (have j1 := eq92 X0 X0
       grind)
    | exact resolve eq56 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq823 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq826 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq809 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq831 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq826 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq826
    | (have j0 := eq826 X0
       grind)
    | exact resolve eq826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq3323 : ∀ X0 : G, (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq823 (τ X0)
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq823
    | (have j0 := eq823 (τ X0)
       grind)
    | exact resolve eq823 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3335 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3323 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3323
    | (have j0 := eq3323 X0
       grind)
    | exact resolve eq3323 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323
  have eq3348 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3335 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3335
    | (have j0 := eq3335 X0
       grind)
    | exact resolve eq3335 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3335
  have eq5457 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq831 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq831
    | exact resolve eq831 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq5550 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 (σ (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5457 X0
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq5457
    | (have j0 := eq5457 X0
       grind)
    | exact resolve eq5457 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5457
  have eq5568 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5550 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5550
    | (have j0 := eq5550 X0
       grind)
    | exact resolve eq5550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5550
  have eq5578 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5568 X0
       have i₂ := eq40 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq40 eq5568
    | (have j0 := eq5568 X0
       grind)
    | exact resolve eq5568 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5568
  have eq5588 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k X0 (σ (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5578 X0
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq5578
    | (have j0 := eq5578 X0
       grind)
    | exact resolve eq5578 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq5578
  have eq5595 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5588 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5588
    | (have j0 := eq5588 X0
       grind)
    | exact resolve eq5588 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5588
  have eq5668 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op x X0)) ∨ (M.op x x) = X0 ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq30 eq292
    | exact resolve eq292 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq5703 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ (M.op x x) = X0 ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq37 eq5668
    | (have j0 := eq5668 X0
       grind)
    | exact resolve eq5668 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq5668
  have eq16417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16417
    | exact resolve eq16417 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16417
  have eq16429 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16418
       have r₂ := eq29
       grind)
    | exact resolve eq16418 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16418
  have eq16434 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  have eq16438 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16429 eq56
    | exact resolve eq56 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16429
  have eq16456 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq16434
  have eq16457 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16438
    | exact resolve eq16438 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16438
  have eq16461 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq16457
  have eq16495 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16461
    | exact resolve eq16461 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16461
  have eq16787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16495 eq112
    | exact resolve eq112 eq16495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16495
  have eq16797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16787
  have eq16799 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16797
       have r₂ := eq29
       grind)
    | exact resolve eq16797 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16797
  have eq17067 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq16799
       grind)
    | exact superpose eq16799 eq109
    | exact resolve eq109 eq16799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq16799
  have eq17094 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17067
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq17067
    | exact resolve eq17067 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17067
  have eq18773 : (τ (σ y)) = (k x x) ∨ x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17094 eq51
    | exact resolve eq51 eq17094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18794 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17094 eq3348
    | (have j0 := eq3348 (σ x)
       grind)
    | exact resolve eq3348 eq17094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348 eq17094
  have eq18803 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq18794
    | exact resolve eq18794 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18794
  have eq18804 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq18803
  have eq18813 : y = (k x x) ∨ x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq18773
    | exact resolve eq18773 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18773
  have eq18983 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq18804 eq582
    | (have r₁ := eq582 (σ x)
       have r₂ := eq18804
       grind)
    | exact resolve eq582 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18804
  have eq18996 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq18983
  have eq19158 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq18996 eq51
    | exact resolve eq51 eq18996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq18996
  have eq19210 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq19158
    | exact resolve eq19158 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19158
  have eq22424 : x = y ∨ x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18813
       have i₂ := eq19210
       grind)
    | exact superpose eq19210 eq18813
    | exact resolve eq18813 eq19210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18813 eq19210
  have eq22448 : x = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22424
  have eq22481 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq22448
       grind)
    | exact superpose eq22448 eq108
    | exact resolve eq108 eq22448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq22483 : (M.op x y) = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22448
  have eq22504 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22481
  have eq22518 : (M.op x y) = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22483
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq22483
    | exact resolve eq22483 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22483
  have eq22519 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22504
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22504
    | exact resolve eq22504 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22504
  have eq23045 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq22518
       grind)
    | exact superpose eq22518 eq46
    | exact resolve eq46 eq22518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22518
  have eq23070 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq23045
    | exact resolve eq23045 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23045
  have eq23087 : (τ (σ x)) = (k y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22519 eq86
    | exact resolve eq86 eq22519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23109 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22519 eq5595
    | (have j0 := eq5595 (σ y)
       grind)
    | exact resolve eq5595 eq22519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595 eq22519
  have eq23117 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq23109
    | exact resolve eq23109 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23109
  have eq23126 : x = (k y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq23087
    | exact resolve eq23087 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23087
  have eq30012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23117 eq23070
    | exact resolve eq23070 eq23117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23070 eq23117
  have eq30016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq30012
  have eq30036 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq30016
       have r₂ := eq29
       grind)
    | exact resolve eq30016 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30016
  have eq30314 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30036 eq582
    | (have r₁ := eq582 (σ y)
       have r₂ := eq30036
       grind)
    | exact resolve eq582 eq30036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30036
  have eq30327 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq30314
  have eq30598 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30327 eq86
    | exact resolve eq86 eq30327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq30327
  have eq30668 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq31 eq30598
    | exact resolve eq30598 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq30598
  have eq31214 : x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq23126
       have i₂ := eq30668
       grind)
    | exact superpose eq30668 eq23126
    | exact resolve eq23126 eq30668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23126 eq30668
  have eq31238 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31214
  have eq31538 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq31238 eq29
    | exact resolve eq29 eq31238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31238
  have eq56668 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16456 eq112
    | exact resolve eq112 eq16456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16456
  have eq56702 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq56668
  have eq56725 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq56702
  have eq56758 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq56725
    | exact resolve eq56725 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56725
  have eq56787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq56758 eq112
    | exact resolve eq112 eq56758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq56758
  have eq56860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq56787
  have eq56864 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq56860
       have r₂ := eq29
       grind)
    | exact resolve eq56860 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56860
  have eq56876 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq56864
       grind)
    | exact superpose eq56864 eq56
    | exact resolve eq56 eq56864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq56864
  have eq56896 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq56876
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq56876
    | exact resolve eq56876 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56876
  have eq56903 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq56896
  have eq56938 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq56903
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq56903
    | exact resolve eq56903 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56903
  have eq57004 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq46
       have i₂ := eq56938
       grind)
    | exact superpose eq56938 eq46
    | exact resolve eq46 eq56938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56938
  have eq57055 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq22 eq57004
    | exact resolve eq57004 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57004
  have eq57139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq57055 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq57055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq57139
    | exact resolve eq57139 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57139
  have eq57159 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq57148
       have r₂ := eq29
       grind)
    | exact resolve eq57148 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57148
  have eq59470 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq57159
  have eq59493 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq59470
  have eq60165 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq59493 eq57055
    | exact resolve eq57055 eq59493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59493
  have eq60170 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq60165
  have eq60215 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq60170
  have eq60249 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq60215
    | exact resolve eq60215 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60215
  have eq60841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq60249 eq57055
    | exact resolve eq57055 eq60249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57055 eq60249
  have eq60849 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq60841
  have eq60867 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq60849
       have r₂ := eq29
       grind)
    | exact resolve eq60849 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60849
  have eq61378 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60867 eq30
    | exact resolve eq30 eq60867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq60867
  have eq61597 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq61378
    | exact resolve eq61378 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq61378
  have eq61598 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61597 eq22
    | exact resolve eq22 eq61597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61743 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq61597
  have eq61867 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61598
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq61598
    | exact resolve eq61598 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61598
  have eq62001 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq61867 eq31538
    | (have r₁ := eq31538
       have r₂ := eq61867
       grind)
    | exact resolve eq31538 eq61867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61867
  have eq62041 : x = y ∨ x = (M.op x y) := by grind
  clear eq62001
  have eq62060 : x = (M.op x y) := by
    first
    | (have r₁ := eq62041
       have r₂ := eq61743
       grind)
    | exact resolve eq62041 eq61743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61743 eq62041
  have eq62182 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq62060 eq22
    | exact resolve eq22 eq62060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62184 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq62060 eq52
    | exact resolve eq52 eq62060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq62471 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq62184
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq62184
    | exact resolve eq62184 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62184
  have eq62473 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq62182
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62182
    | exact resolve eq62182 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62182
  have eq62479 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq62060 eq62471
    | exact resolve eq62471 eq62060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62471
  have eq62483 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq62479
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq62479
    | exact resolve eq62479 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62479
  have eq62486 : x = (M.op x x) := by
    first
    | exact superpose eq62060 eq62483
    | exact resolve eq62483 eq62060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62483
  have eq62488 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq62473 eq28
    | exact resolve eq28 eq62473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq62713 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq582 x
       have i₂ := eq62486
       grind)
    | exact superpose eq62486 eq582
    | (have r₁ := eq582 x
       have r₂ := eq62486
       grind)
    | exact resolve eq582 eq62486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq62727 : x = (k x x) := by grind
  clear eq62713
  have eq64001 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq823 x
       have i₂ := eq62727
       grind)
    | exact superpose eq62727 eq823
    | (have j0 := eq823 x
       grind)
    | exact resolve eq823 eq62727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823 eq62727
  have eq64021 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq64001
  have eq64037 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq64021
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq64021
    | exact resolve eq64021 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64021
  have eq64059 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq62473 eq64037
    | exact resolve eq64037 eq62473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64037
  have eq104093 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ x = X0 ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq5703 X0
       have i₂ := eq62486
       grind)
    | exact superpose eq62486 eq5703
    | (have j0 := eq5703 X0
       grind)
    | exact resolve eq5703 eq62486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703
  have eq104174 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq104093 y
       grind)
    | exact superpose eq104093 eq46
    | (have j1 := eq104093 y
       grind)
    | exact resolve eq46 eq104093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq104093
  have eq104392 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq62473 eq104174
    | exact resolve eq104174 eq62473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104174
  have eq104475 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq104392
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq104392
    | exact resolve eq104392 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104392
  have eq104514 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq104475
    | exact resolve eq104475 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq104475
  have eq104600 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq104514 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq104514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq62488 eq104600
    | exact resolve eq104600 eq62488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104600
  have eq104614 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq104601
       have r₂ := eq29
       grind)
    | exact resolve eq104601 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104601
  have eq104626 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq64059 eq104614
    | exact resolve eq104614 eq64059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104614
  have eq104638 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq104626
       have r₂ := eq31538
       grind)
    | exact resolve eq104626 eq31538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31538 eq104626
  have eq104800 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq104638
  have eq104852 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq62488 eq104800
    | exact resolve eq104800 eq62488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104800
  have eq107597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq104852 eq104514
    | exact resolve eq104514 eq104852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104514 eq104852
  have eq107602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq107597
  have eq107608 : x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq107602
       have r₂ := eq29
       grind)
    | exact resolve eq107602 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107602
  have eq107634 : y = (M.op (M.op (M.op x x) x) y) ∨ x = y := by
    first
    | (have i₁ := eq209 y
       have i₂ := eq107608
       grind)
    | exact superpose eq107608 eq209
    | exact resolve eq209 eq107608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq107608
  have eq107666 : y = (M.op (M.op x x) y) ∨ x = y := by
    first
    | (have i₁ := eq107634
       have i₂ := eq62486
       grind)
    | exact superpose eq62486 eq107634
    | exact resolve eq107634 eq62486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107634
  have eq107687 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq107666
       have i₂ := eq62486
       grind)
    | exact superpose eq62486 eq107666
    | exact resolve eq107666 eq62486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62486 eq107666
  have eq107705 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq107687
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq107687
    | exact resolve eq107687 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq107687
  have eq107716 : x = y ∨ x = y := by
    first
    | exact superpose eq62060 eq107705
    | exact resolve eq107705 eq62060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62060 eq107705
  have eq107717 : x = y := by grind
  clear eq107716
  have eq107727 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq107717
       grind)
    | exact superpose eq107717 eq26
    | exact resolve eq26 eq107717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq107717
  have eq108074 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq107727
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq107727
    | exact resolve eq107727 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq107727
  have eq108203 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq62473 eq108074
    | exact resolve eq108074 eq62473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62473 eq108074
  have eq108563 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq108203 eq62488
    | exact resolve eq62488 eq108203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62488 eq108203
  have eq108575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64059 eq108563
    | exact resolve eq108563 eq64059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64059 eq108563
  have eq108699 : False := by grind
  exact eq108699

/-- `Equation3078`: `x = (((x ◇ y) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_y_pyy_pyx_Equation3078 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3078 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3078.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq16 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X1) X0) = X0 := by
    intro X0 X1
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : x = (M.op (M.op (M.op (M.op x y) y) y) x) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op X0 X0) X0
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq41
    | exact resolve eq41 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq183 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq182
    | exact resolve eq182 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq226 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq141
    | exact resolve eq141 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq247 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq226
    | exact resolve eq226 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq345 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq729 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq730 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq758 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq759 X0
       grind)
    | exact superpose eq759 eq179
    | (have j1 := eq759 X0
       grind)
    | exact resolve eq179 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq785 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq1664 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq729
       grind)
    | exact superpose eq729 eq39
    | exact resolve eq39 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq1665 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1664
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1664
    | exact resolve eq1664 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664
  have eq1667 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1665
    | exact resolve eq1665 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq16579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1667 eq730
    | exact resolve eq730 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16588 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16579
       have r₂ := eq27
       grind)
    | exact resolve eq16579 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16579
  have eq16595 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16588 eq758
    | (have r₁ := eq758
       have r₂ := eq16588
       grind)
    | exact resolve eq758 eq16588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16611 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq16588
  have eq16613 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq16595
  have eq16614 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16613
       have r₂ := eq16611
       grind)
    | exact resolve eq16613 eq16611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16611 eq16613
  have eq16615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1667 eq16614
    | exact resolve eq16614 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16614
  have eq16616 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16615
       have r₂ := eq27
       grind)
    | exact resolve eq16615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16615
  have eq16619 : x = (k (τ (σ y)) x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16616 eq247
    | exact resolve eq247 eq16616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16622 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16616 eq174
    | exact resolve eq174 eq16616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq16625 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16616 eq179
    | exact resolve eq179 eq16616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16616
  have eq16636 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq16625
    | exact resolve eq16625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16625
  have eq16637 : x = (k y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq16619
    | exact resolve eq16619 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16619
  have eq16638 : (M.op x y) = (M.op x x) ∨ x = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16637
       have r₂ := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq16637
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16637 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16637
  have eq16640 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq757
       have i₂ := eq16638
       grind)
    | exact superpose eq16638 eq757
    | (have r₁ := eq757
       have r₂ := eq16638
       grind)
    | exact resolve eq757 eq16638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16638
  have eq16657 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq16640
  have eq16696 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq757
       have i₂ := eq16636
       grind)
    | exact superpose eq16636 eq757
    | (have r₁ := eq757
       have r₂ := eq16636
       grind)
    | exact resolve eq757 eq16636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16712 : y ≠ (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq16636
  have eq16714 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq16696
  have eq16716 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16714
       have r₂ := eq16712
       grind)
    | exact resolve eq16714 eq16712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16714
  have eq16807 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq16657
       grind)
    | exact superpose eq16657 eq39
    | exact resolve eq39 eq16657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16657
  have eq16810 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16807
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16807
    | exact resolve eq16807 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16807
  have eq16814 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq16810
    | exact resolve eq16810 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16810
  have eq16931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq16814 eq730
    | exact resolve eq730 eq16814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16940 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq16931
       have r₂ := eq27
       grind)
    | exact resolve eq16931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16931
  have eq17053 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16622 eq1667
    | exact resolve eq1667 eq16622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667 eq16622
  have eq17060 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq17053
  have eq17077 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq757
       have i₂ := eq17060
       grind)
    | exact superpose eq17060 eq757
    | (have r₁ := eq757
       have r₂ := eq17060
       grind)
    | exact resolve eq757 eq17060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq17094 : y ≠ (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq17060
  have eq17096 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq17077
  have eq17098 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17096
       have r₂ := eq17094
       grind)
    | exact resolve eq17096 eq17094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17096
  have eq17185 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq17098
       grind)
    | exact superpose eq17098 eq39
    | exact resolve eq39 eq17098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17098
  have eq17188 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17185
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17185
    | exact resolve eq17185 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17185
  have eq17192 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq17188
    | exact resolve eq17188 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17188
  have eq18919 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq16940 eq758
    | (have r₁ := eq758
       have r₂ := eq16940
       grind)
    | exact resolve eq758 eq16940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq18940 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq16940
  have eq18944 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq18919
  have eq18949 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq18944
       have r₂ := eq18940
       grind)
    | exact resolve eq18944 eq18940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18940 eq18944
  have eq18955 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq16814 eq18949
    | exact resolve eq18949 eq16814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16814 eq18949
  have eq18957 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq18955
       have r₂ := eq27
       grind)
    | exact resolve eq18955 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18955
  have eq18966 : x = (k (τ (σ y)) x) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq18957 eq247
    | exact resolve eq247 eq18957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18957
  have eq18994 : x = (k y x) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq31 eq18966
    | exact resolve eq18966 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18966
  have eq18995 : x = (k y x) ∨ y = (M.op x y) := by grind
  clear eq18994
  have eq19008 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16716
       have i₂ := eq18995
       grind)
    | exact superpose eq18995 eq16716
    | exact resolve eq16716 eq18995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16716
  have eq19011 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq18995
       grind)
    | exact superpose eq18995 eq36
    | exact resolve eq36 eq18995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18995
  have eq19017 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19011
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19011
    | exact resolve eq19011 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19011
  have eq19020 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19008
       have r₂ := eq16712
       grind)
    | exact resolve eq19008 eq16712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16712 eq19008
  have eq19041 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19017 eq17192
    | exact resolve eq17192 eq19017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17192
  have eq19045 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq19041
  have eq19052 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq19045
       have r₂ := eq17094
       grind)
    | exact resolve eq19045 eq17094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17094 eq19045
  have eq19078 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq19052
       grind)
    | exact superpose eq19052 eq179
    | exact resolve eq179 eq19052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq19052
  have eq19090 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19078
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19078
    | exact resolve eq19078 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19078
  have eq19092 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19090 eq28
    | exact resolve eq28 eq19090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19090
  have eq19207 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq19092
    | exact resolve eq19092 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19092
  have eq19226 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq19207
       grind)
    | exact superpose eq19207 eq24
    | exact resolve eq24 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq19300 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq19226
    | exact resolve eq19226 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19226
  have eq20305 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq19020
       grind)
    | exact superpose eq19020 eq12
    | exact resolve eq12 eq19020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19020
  have eq20311 : x = y ∨ y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20305
  have eq20319 : x = (M.op x y) ∨ y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19207 eq20311
    | exact resolve eq20311 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20311
  have eq20320 : x = (M.op x y) ∨ y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20319
  have eq20336 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19207 eq20320
    | exact resolve eq20320 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19207 eq20320
  have eq20366 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq20336
       grind)
    | exact superpose eq20336 eq39
    | exact resolve eq39 eq20336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq20380 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20366
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20366
    | exact resolve eq20366 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20366
  have eq20384 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq20380
    | exact resolve eq20380 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20380
  have eq20388 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19300 eq20384
    | exact resolve eq20384 eq19300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20384
  have eq20471 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20388 eq767
    | (have j0 := eq767 (σ x)
       grind)
    | exact resolve eq767 eq20388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq20388
  have eq20487 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq20471
    | exact resolve eq20471 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20471
  have eq20488 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20487
  have eq20729 : x = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20488 eq247
    | exact resolve eq247 eq20488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq20488
  have eq20756 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq20729
    | exact resolve eq20729 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20729
  have eq20762 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20336 eq20756
    | exact resolve eq20756 eq20336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20336 eq20756
  have eq20763 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20762
  have eq20764 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20763 eq27
    | exact resolve eq27 eq20763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20763
  have eq20770 : x = (M.op x y) := by
    first
    | (have r₁ := eq20764
       have r₂ := eq19300
       grind)
    | exact resolve eq20764 eq19300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19300 eq20764
  have eq20771 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20770
       grind)
    | exact superpose eq20770 eq18
    | exact resolve eq18 eq20770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20772 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq20770
       grind)
    | exact superpose eq20770 eq22
    | exact resolve eq22 eq20770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq20903 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20772 eq20
    | exact resolve eq20 eq20772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20973 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20772 eq345
    | exact resolve eq345 eq20772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq20772
  have eq21355 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq20771 eq175
    | exact resolve eq175 eq20771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq21366 : (M.op x y) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq21355
       have i₂ := eq20770
       grind)
    | exact superpose eq20770 eq21355
    | exact resolve eq21355 eq20770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21355
  have eq21372 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20771 eq21366
    | exact resolve eq21366 eq20771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20771 eq21366
  have eq21381 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21372 eq183
    | exact resolve eq183 eq21372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq21387 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21372 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq21372
       grind)
    | exact resolve eq13 eq21372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21372
  have eq21406 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20903 eq21381
    | exact resolve eq21381 eq20903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21381
  have eq21413 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq21406
    | exact resolve eq21406 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21406
  have eq21414 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20903 eq21413
    | exact resolve eq21413 eq20903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21413
  have eq21469 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21414 eq785
    | (have j0 := eq785 (σ x)
       grind)
    | (have r₁ := eq785 (σ x)
       have r₂ := eq21414
       grind)
    | exact resolve eq785 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq21414
  have eq21470 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21469
  have eq22846 : (τ (σ x)) = (k (τ (σ y)) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19017 eq20973
    | exact resolve eq20973 eq19017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19017 eq20973
  have eq23016 : (τ (σ x)) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq22846
    | exact resolve eq22846 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq22846
  have eq23081 : x = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq23016
    | exact resolve eq23016 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23016
  have eq23121 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23081
       have i₂ := eq20770
       grind)
    | exact superpose eq20770 eq23081
    | exact resolve eq23081 eq20770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20770 eq23081
  have eq23138 : (M.op x y) = (k y (M.op x y)) := by
    first
    | (have j1 := eq21387 y
       grind)
    | (have r₁ := eq23121
       have r₂ := eq21387 (k y (M.op x y))
       grind)
    | (have r₁ := eq23121
       have r₂ := eq21387 y
       grind)
    | exact resolve eq23121 eq21387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21387 eq23121
  have eq23152 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq23138 eq36
    | exact resolve eq36 eq23138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq23138
  have eq23158 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq23152
    | exact resolve eq23152 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq23152
  have eq23164 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20903 eq23158
    | exact resolve eq23158 eq20903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23158
  have eq23181 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23164 eq730
    | exact resolve eq730 eq23164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq23164
  have eq23196 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21470 eq23181
    | exact resolve eq23181 eq21470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23181
  have eq23197 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq23196
  have eq23207 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21470 eq23197
    | exact resolve eq23197 eq21470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23197
  have eq23216 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23207 eq27
    | exact resolve eq27 eq23207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23207
  have eq23231 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq23216
       have r₂ := eq20903
       grind)
    | exact resolve eq23216 eq20903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23216
  have eq23236 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23231 eq26
    | exact resolve eq26 eq23231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq23231
  have eq23358 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21470 eq23236
    | exact resolve eq23236 eq21470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21470 eq23236
  have eq23450 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq23358 eq27
    | exact resolve eq27 eq23358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23358
  have eq23463 : False := by grind
  exact eq23463

/-- `Equation3078`: `x = (((x ◇ y) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pxy_pyx_Equation3078 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3078 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3078.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X1) X0) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq111 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq111
    | exact resolve eq111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq151 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq154 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq149
    | (have j0 := eq149 X0 X1
       grind)
    | exact resolve eq149 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq851 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq151
    | exact resolve eq151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq901 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq3419 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq154 x y
       grind)
    | exact superpose eq154 eq16
    | (have j1 := eq154 x y
       grind)
    | exact resolve eq16 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq5879 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3419
       have i₂ := eq901 y x
       grind)
    | exact superpose eq901 eq3419
    | (have j1 := eq901 y x
       grind)
    | (have r₁ := eq3419
       have r₂ := eq901 y x
       grind)
    | (have r₁ := eq3419
       have r₂ := eq901 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3419
       have r₂ := eq901 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3419 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq3419
  have eq5880 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq5879
  have eq5882 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5880
       grind)
    | exact superpose eq5880 eq16
    | exact resolve eq16 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5880
  have eq5883 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5882
       have r₂ := eq23 x
       grind)
    | exact resolve eq5882 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5882
  have eq5885 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5883
       grind)
    | exact superpose eq5883 eq10
    | exact resolve eq10 eq5883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5883
  have eq5939 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5885
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5885
    | exact resolve eq5885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5885
  have eq5941 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5939
       grind)
    | exact superpose eq5939 eq16
    | exact resolve eq16 eq5939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5939
  have eq5942 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5941
       have r₂ := eq23 x
       grind)
    | exact resolve eq5941 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5941
  have eq5952 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq111 x
       have i₂ := eq5942
       grind)
    | exact superpose eq5942 eq111
    | exact resolve eq111 eq5942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5953 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq5942
       grind)
    | exact superpose eq5942 eq112
    | exact resolve eq112 eq5942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5942
  have eq5994 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5953
       grind)
    | exact superpose eq5953 eq16
    | exact resolve eq16 eq5953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953
  have eq6024 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5994
       have i₂ := eq5952
       grind)
    | exact superpose eq5952 eq5994
    | exact resolve eq5994 eq5952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5952 eq5994
  have eq6025 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq6024
  have eq6026 : (σ y) = (σ (M.op x x)) := by grind
  clear eq6025
  have eq6033 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq6026
       grind)
    | exact superpose eq6026 eq112
    | exact resolve eq112 eq6026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq6041 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq6026
       grind)
    | exact superpose eq6026 eq10
    | exact resolve eq10 eq6026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6026
  have eq6095 : y = (M.op x x) := by
    first
    | (have i₁ := eq6041
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6041
    | exact resolve eq6041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6041
  have eq6107 : y = (M.op x y) := by
    first
    | (have i₁ := eq111 x
       have i₂ := eq6095
       grind)
    | exact superpose eq6095 eq111
    | exact resolve eq111 eq6095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq6095
  have eq6158 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6033
       grind)
    | exact superpose eq6033 eq16
    | exact resolve eq16 eq6033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6033
  have eq6167 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6158
       have i₂ := eq6107
       grind)
    | exact superpose eq6107 eq6158
    | exact resolve eq6158 eq6107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6107 eq6158
  have eq6168 : False := by grind
  exact eq6168

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pxy_x_pxy_Equation3081 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq64 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
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
  have eq70 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq84
    | (have j0 := eq84 (σ X0) (σ X1)
       grind)
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq115
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq139 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq143 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq65
    | exact resolve eq65 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq144 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq139 eq16
    | exact resolve eq16 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq448 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq70
    | (have r₁ := eq70
       have r₂ := eq129
       grind)
    | exact resolve eq70 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq129
  have eq449 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq448
  have eq450 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq449
       have r₂ := eq143
       grind)
    | exact resolve eq449 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq449
  have eq453 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq450 eq116
    | exact resolve eq116 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq450
  have eq457 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq453
  have eq462 : x = (M.op x y) := by
    first
    | (have r₁ := eq457
       have r₂ := eq144
       grind)
    | exact resolve eq457 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq457
  have eq465 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq462 eq20
    | exact resolve eq20 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq462 eq64
    | exact resolve eq64 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq469 : x ≠ x ∨ x = y ∨ x = (k x y) := by
    first
    | exact superpose eq462 eq69
    | (have r₁ := eq69
       have r₂ := eq462
       grind)
    | exact resolve eq69 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq476 : x = y ∨ x = (k x y) := by grind
  clear eq469
  have eq483 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq465
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq465
    | exact resolve eq465 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq549 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq483 eq26
    | exact resolve eq26 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq615 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq96
    | (have j0 := eq96 (M.op x y) X0
       grind)
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq96
  have eq651 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq462 eq615
    | (have j0 := eq615 X0
       grind)
    | exact resolve eq615 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq1091 : (σ (k x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq651 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq651
    | (have j0 := eq651 y
       grind)
    | exact resolve eq651 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq651
  have eq1109 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq549 eq1091
    | exact resolve eq1091 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1122 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1109
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1109
    | exact resolve eq1109 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1109
  have eq1131 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq483 eq1122
    | exact resolve eq1122 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq549 eq1131
    | exact resolve eq1131 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq1131
  have eq1144 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq1138
       have r₂ := eq27
       grind)
    | exact resolve eq1138 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1153 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq1144 eq168
    | exact resolve eq168 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq1144
  have eq1155 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq462 eq1153
    | exact resolve eq1153 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq1153
  have eq1374 : x ≠ y ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq468
       have i₂ := eq1155
       grind)
    | exact superpose eq1155 eq468
    | exact resolve eq468 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq1375 : x = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq476
       have i₂ := eq1155
       grind)
    | exact superpose eq1155 eq476
    | exact resolve eq476 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq1155
  have eq1376 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1375
       have r₂ := eq1374
       grind)
    | exact resolve eq1375 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374 eq1375
  have eq1406 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1376 eq15
    | exact resolve eq15 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq1407 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1406
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1406
    | exact resolve eq1406 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1406
  have eq1408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq483 eq1407
    | exact resolve eq1407 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq1407
  have eq1409 : False := by grind
  exact eq1409

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pyy_pyx_Equation3081 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X1 X0
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) ≠ X0 ∨ (k X0 (M.op (M.op (M.op X0 X1) X1) X2)) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) (M.op (M.op (M.op X0 X1) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X0 X1) X1) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X0 X1) X1) X2)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X0) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq118 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq677 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op (σ X0) (σ X0)) X1) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq73 (σ X0) X1
       grind)
    | exact superpose eq73 eq15
    | (have j1 := eq73 (σ X0) X1
       grind)
    | exact resolve eq15 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq5387 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq16
    | (have j1 := eq118 x y
       grind)
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5426 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq11469 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120
    | exact resolve eq120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq11564 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11469 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11469
    | (have j0 := eq11469 X0 X1
       grind)
    | exact resolve eq11469 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11469
  have eq36480 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5387
       have i₂ := eq11564 y x
       grind)
    | exact superpose eq11564 eq5387
    | (have j1 := eq11564 (σ x) (σ y)
       grind)
    | (have r₁ := eq5387
       have r₂ := eq11564 y x
       grind)
    | (have r₁ := eq5387
       have r₂ := eq11564 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5387
       have r₂ := eq11564 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5387 eq11564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5387
  have eq36481 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq36480
  have eq49447 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69 (σ X0) (σ X0) (σ X0)
       have i₂ := eq677 X0 (σ X0)
       grind)
    | exact superpose eq677 eq69
    | (have j1 := eq677 X0 x
       grind)
    | (have r₁ := eq69 (σ X0) (σ X0) (σ X0)
       have r₂ := eq677 X0 (σ X0)
       grind)
    | exact resolve eq69 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq677
  have eq49524 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq49447 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49447
  have eq49526 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq49524 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq49524
    | (have j0 := eq49524 X0
       grind)
    | exact resolve eq49524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49524
  have eq49527 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq49526 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49526
  have eq49624 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49527 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49527
    | exact resolve eq49527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49906 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq49624 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq49624
    | exact resolve eq49624 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq49624
  have eq49980 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq49906 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49906
    | exact resolve eq49906 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49906
  have eq213118 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36481
       grind)
    | exact superpose eq36481 eq16
    | exact resolve eq16 eq36481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36481
  have eq213119 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq213118
       have i₂ := eq49527 x
       grind)
    | exact superpose eq49527 eq213118
    | exact resolve eq213118 eq49527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213118
  have eq213120 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq213119
       have i₂ := eq49980 x
       grind)
    | exact superpose eq49980 eq213119
    | exact resolve eq213119 eq49980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213119
  have eq213121 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq213120
  have eq213123 : x ≠ x ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq213121
       grind)
    | exact superpose eq213121 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq213121
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq213121
       grind)
    | exact resolve eq12 eq213121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213127 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq213121
       grind)
    | exact superpose eq213121 eq64
    | exact resolve eq64 eq213121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213121
  have eq213176 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq213123
  have eq213193 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 (σ x) (σ y)
       have i₂ := eq213127
       grind)
    | exact superpose eq213127 eq64
    | exact resolve eq64 eq213127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq213127
  have eq213246 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq213193
       have i₂ := eq49527 x
       grind)
    | exact superpose eq49527 eq213193
    | exact resolve eq213193 eq49527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213193
  have eq213256 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq213246
       have i₂ := eq49980 x
       grind)
    | exact superpose eq49980 eq213246
    | exact resolve eq213246 eq49980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213246
  have eq213277 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq213256
       grind)
    | exact superpose eq213256 eq10
    | exact resolve eq10 eq213256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213256
  have eq213439 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq213277
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq213277
    | exact resolve eq213277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213277
  have eq213541 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq213439
       grind)
    | exact superpose eq213439 eq16
    | exact resolve eq16 eq213439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213439
  have eq213542 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq213541
       have i₂ := eq49527 x
       grind)
    | exact superpose eq49527 eq213541
    | exact resolve eq213541 eq49527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213541
  have eq213543 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq213542
       have i₂ := eq49980 x
       grind)
    | exact superpose eq49980 eq213542
    | exact resolve eq213542 eq49980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213542
  have eq213544 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq213543
  have eq213561 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq213544
       grind)
    | exact superpose eq213544 eq10
    | exact resolve eq10 eq213544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213544
  have eq213726 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq213561
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq213561
    | exact resolve eq213561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213561
  have eq213727 : x = (M.op x x) := by grind
  clear eq213726
  have eq275772 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5426 x y
       have i₂ := eq213176
       grind)
    | exact superpose eq213176 eq5426
    | (have j0 := eq5426 x y
       grind)
    | exact resolve eq5426 eq213176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5426 eq213176
  have eq275788 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq275772
  have eq275795 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq275788
       have i₂ := eq213727
       grind)
    | exact superpose eq213727 eq275788
    | exact resolve eq275788 eq213727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275788
  have eq275796 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq275795
  have eq275800 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq275796
       grind)
    | exact superpose eq275796 eq10
    | exact resolve eq10 eq275796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275796
  have eq275968 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq275800
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq275800
    | exact resolve eq275800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275800
  have eq276109 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275968
       grind)
    | exact superpose eq275968 eq16
    | exact resolve eq16 eq275968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275968
  have eq276110 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq276109
       have i₂ := eq49527 x
       grind)
    | exact superpose eq49527 eq276109
    | exact resolve eq276109 eq49527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276109
  have eq276111 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq276110
       have i₂ := eq49980 x
       grind)
    | exact superpose eq49980 eq276110
    | exact resolve eq276110 eq49980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276110
  have eq276112 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq276111
  have eq276120 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq276112
       grind)
    | exact superpose eq276112 eq16
    | exact resolve eq16 eq276112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276145 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq276112
       grind)
    | exact superpose eq276112 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq276112
       grind)
    | exact resolve eq12 eq276112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276112
  have eq276199 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
  clear eq276145
  have eq276204 : (k (σ y) (σ x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq276199
       have i₂ := eq49527 x
       grind)
    | exact superpose eq49527 eq276199
    | exact resolve eq276199 eq49527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49527 eq276199
  have eq276220 : (k (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq276204
       have i₂ := eq49980 x
       grind)
    | exact superpose eq49980 eq276204
    | exact resolve eq276204 eq49980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49980 eq276204
  have eq276228 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq276220
       have i₂ := eq213727
       grind)
    | exact superpose eq213727 eq276220
    | exact resolve eq276220 eq213727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276220
  have eq276229 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq276228
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq276228
    | exact resolve eq276228 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276228
  have eq276281 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11564 y x
       have i₂ := eq276229
       grind)
    | exact superpose eq276229 eq11564
    | (have j0 := eq11564 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11564 eq276229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11564 eq276229
  have eq276453 : x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq276281
       have r₂ := eq276120
       grind)
    | exact resolve eq276281 eq276120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276281
  have eq276625 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq276120
       have i₂ := eq276453
       grind)
    | exact superpose eq276453 eq276120
    | exact resolve eq276120 eq276453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276453
  have eq276630 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq276625
       have i₂ := eq213727
       grind)
    | exact superpose eq213727 eq276625
    | exact resolve eq276625 eq213727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213727 eq276625
  have eq276631 : x = (M.op x y) := by grind
  clear eq276630
  have eq276638 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq276120
       have i₂ := eq276631
       grind)
    | exact superpose eq276631 eq276120
    | exact resolve eq276120 eq276631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276120 eq276631
  have eq276759 : False := by grind
  exact eq276759

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation3081 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
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
  clear eq22
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X0 X1) X1) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X0 X1) X1) X2) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X0 X1) X1) X2) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq75 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq44
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ y) (σ y)) X0) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq127 eq51
    | exact resolve eq51 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq232 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq226 eq14
    | exact resolve eq14 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq232
    | (have j0 := eq232 (σ y)
       grind)
    | exact resolve eq232 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq263 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) X0) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq253 eq14
    | exact resolve eq14 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq266 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq226 eq263
    | exact resolve eq263 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq263
  have eq276 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq266
  have eq303 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq276 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq276
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq276
       grind)
    | exact resolve eq12 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq305 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq303
  have eq318 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq305
    | exact resolve eq305 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq305
  have eq323 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq318
  have eq353 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq323 eq118
    | exact resolve eq118 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq357 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq353
  have eq362 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq357
       have r₂ := eq129
       grind)
    | exact resolve eq357 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq357
  have eq371 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq362 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq362
       grind)
    | exact resolve eq13 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq372 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq372 eq118
    | exact resolve eq118 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq372
  have eq394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq390
  have eq399 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq394
    | exact resolve eq394 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq401 : y = (M.op x y) := by
    first
    | (have r₁ := eq399
       have r₂ := eq27
       grind)
    | exact resolve eq399 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq403 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq401 eq20
    | exact resolve eq20 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq403
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq403
    | exact resolve eq403 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq422 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq419 eq26
    | exact resolve eq26 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq552 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq50 eq76
    | (have j0 := eq76 (M.op x y) x x
       grind)
    | exact resolve eq76 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq76
  have eq567 : y = (k x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq401 eq552
    | exact resolve eq552 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq575 : y = (k x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq401 eq567
    | exact resolve eq567 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq567
  have eq849 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq575
       grind)
    | exact superpose eq575 eq44
    | exact resolve eq44 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq856 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq419 eq849
    | exact resolve eq849 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq858 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq856
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq856
    | exact resolve eq856 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq856
  have eq859 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq419 eq858
    | exact resolve eq858 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq900 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq859 eq92
    | (have j0 := eq92 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq901 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by grind
  clear eq900
  have eq903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq422 eq901
    | exact resolve eq901 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq906 : y = (M.op y y) := by
    first
    | (have r₁ := eq903
       have r₂ := eq27
       grind)
    | exact resolve eq903 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq918 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq906
       grind)
    | exact superpose eq906 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq906
       grind)
    | exact resolve eq13 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq919 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq918 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq1023 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq919 x
       grind)
    | exact superpose eq919 eq44
    | exact resolve eq44 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq919
  have eq1031 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq419 eq1023
    | exact resolve eq1023 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq1023
  have eq1035 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1031
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1031
    | exact resolve eq1031 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1031
  have eq1038 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1035
    | exact resolve eq1035 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1035
  have eq1044 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1038 eq92
    | (have j0 := eq92 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1038
  have eq1045 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1044
  have eq1047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq422 eq1045
    | exact resolve eq1045 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq1045
  have eq1050 : False := by grind
  exact eq1050

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxy_pyx_Equation3081 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq25 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X1 X0
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq55 (τ X1) X0
       grind)
    | exact superpose eq55 eq17
    | (have j1 := eq55 (τ X1) X0
       grind)
    | exact resolve eq17 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq132 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq274 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq299 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq274
    | (have j0 := eq274 X0 X1
       grind)
    | exact resolve eq274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq365 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq132
    | (have j1 := eq55 (σ y) (σ x)
       grind)
    | exact resolve eq132 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq368 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq365
  have eq374 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25 x y
       have i₂ := eq368
       grind)
    | exact superpose eq368 eq25
    | exact resolve eq25 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq446 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq374
       grind)
    | exact superpose eq374 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq374
       grind)
    | exact resolve eq12 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq454 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq446 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq1167 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq132
       have i₂ := eq454 y
       grind)
    | exact superpose eq454 eq132
    | exact resolve eq132 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq454
  have eq1168 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1167
  have eq1169 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1168
  have eq1268 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1169
       grind)
    | exact superpose eq1169 eq16
    | exact resolve eq16 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1274 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25 (σ x) (σ y)
       have i₂ := eq1169
       grind)
    | exact superpose eq1169 eq25
    | exact resolve eq25 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1352 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq1274
       grind)
    | exact superpose eq1274 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq1274
       grind)
    | exact resolve eq12 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1371 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq1352 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1494 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1371 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq1371
    | exact resolve eq1371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq2320 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1494 y
       have i₂ := eq1169
       grind)
    | exact superpose eq1169 eq1494
    | exact resolve eq1494 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq1494
  have eq2563 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq299 y x
       have i₂ := eq2320
       grind)
    | exact superpose eq2320 eq299
    | (have j0 := eq299 y x
       grind)
    | exact resolve eq299 eq2320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq2320
  have eq2619 : x = (M.op x y) := by
    first
    | (have r₁ := eq2563
       have r₂ := eq1268
       grind)
    | exact resolve eq2563 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563
  have eq3024 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1268
       have i₂ := eq2619
       grind)
    | exact superpose eq2619 eq1268
    | exact resolve eq1268 eq2619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268 eq2619
  have eq3056 : False := by grind
  exact eq3056

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pyx_Equation3081 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3081 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq111 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X1 X0
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq111 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq111
    | exact resolve eq111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq185 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq188 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | exact resolve eq183 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq3543 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq188 x y
       grind)
    | exact superpose eq188 eq16
    | (have j1 := eq188 x y
       grind)
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq6993 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq185
    | exact resolve eq185 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq7087 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6993 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6993
    | (have j0 := eq6993 X0 X1
       grind)
    | exact resolve eq6993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6993
  have eq20130 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3543
       have i₂ := eq7087 y x
       grind)
    | exact superpose eq7087 eq3543
    | (have j1 := eq7087 y x
       grind)
    | (have r₁ := eq3543
       have r₂ := eq7087 y x
       grind)
    | (have r₁ := eq3543
       have r₂ := eq7087 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3543
       have r₂ := eq7087 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3543 eq7087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3543 eq7087
  have eq20131 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq20130
  have eq20133 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20131
       grind)
    | exact superpose eq20131 eq16
    | exact resolve eq16 eq20131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20131
  have eq20134 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq20133
       have r₂ := eq23 x
       grind)
    | exact resolve eq20133 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20133
  have eq20136 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20134
       grind)
    | exact superpose eq20134 eq10
    | exact resolve eq10 eq20134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20134
  have eq20205 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq20136
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20136
    | exact resolve eq20136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20136
  have eq20207 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20205
       grind)
    | exact superpose eq20205 eq16
    | exact resolve eq16 eq20205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20205
  have eq20208 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq20207
       have r₂ := eq23 x
       grind)
    | exact resolve eq20207 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20207
  have eq20237 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq20208
       grind)
    | exact superpose eq20208 eq10
    | exact resolve eq10 eq20208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20208
  have eq20306 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20237
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq20237
    | exact resolve eq20237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20237
  have eq20307 : y = (M.op x x) := by grind
  clear eq20306
  have eq20312 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq114 x
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq114
    | exact resolve eq114 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq20410 : y = (M.op x y) := by
    first
    | (have i₁ := eq111 x x
       have i₂ := eq20307
       grind)
    | exact superpose eq20307 eq111
    | exact resolve eq111 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq20307
  have eq20506 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20312
       grind)
    | exact superpose eq20312 eq16
    | exact resolve eq16 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20312
  have eq20573 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq20506
       have i₂ := eq20410
       grind)
    | exact superpose eq20410 eq20506
    | exact resolve eq20506 eq20410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20410 eq20506
  have eq20574 : False := by grind
  exact eq20574
