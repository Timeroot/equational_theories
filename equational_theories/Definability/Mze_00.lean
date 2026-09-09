import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1487`: `x = (y ◇ x) ◇ (x ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_y_Equation1487 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) Law1487 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1487.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X3))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq32 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq25
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
  have eq53 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 y x X0 X1
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op x X0) (M.op X0 (M.op x x))
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq79 : y = (M.op (M.op x y) (M.op y (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq92 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq56 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y X0 x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq96 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq79 eq56
    | exact resolve eq56 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq101 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (k (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq56 X0 X0 X0
       grind)
    | exact superpose eq56 eq12
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq65
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq140 : (σ y) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq139
    | exact resolve eq139 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq143 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq106 (σ X0)
       grind)
    | exact superpose eq106 eq15
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq143 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq143
    | exact resolve eq143 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq229 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq10
    | exact resolve eq10 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 : G, (σ (k (M.op X0 X0) y)) = (k (M.op (σ X0) (σ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq36
    | exact resolve eq36 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq274 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq229 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq229
    | exact resolve eq229 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq757 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 (M.op X0 X1)
       have i₂ := eq56 X1 X0 X0
       grind)
    | exact superpose eq56 eq101
    | (have j0 := eq101 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq101 x (M.op x X0)
       have r₂ := eq56 X0 x x
       grind)
    | exact resolve eq101 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq96 eq101
    | (have j0 := eq101 (M.op x y) y
       grind)
    | (have r₁ := eq101 (M.op x y) y
       have r₂ := eq96 (M.op x y)
       grind)
    | exact resolve eq101 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : x ≠ x ∨ x = (k (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq92 eq101
    | (have j0 := eq101 x (M.op x y)
       grind)
    | (have r₁ := eq101 x (M.op x y)
       have r₂ := eq92 x
       grind)
    | exact resolve eq101 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq765 : x = (k (M.op x x) (M.op x y)) := by grind
  clear eq759
  have eq766 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) y) := by grind
  clear eq758
  have eq767 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq757 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq814 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq766 eq127
    | (have j0 := eq127 y (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq127 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq815 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq765 eq127
    | (have j0 := eq127 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq127 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq765
  have eq882 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq815
    | exact resolve eq815 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq883 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq21 eq814
    | exact resolve eq814 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq899 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq882
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq882
    | exact resolve eq882 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq900 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq883
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq883
    | exact resolve eq883 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq914 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq899
       have i₂ := eq144 x
       grind)
    | exact superpose eq144 eq899
    | exact resolve eq899 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq915 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq900
       have i₂ := eq144 sF0
       grind)
    | exact superpose eq144 eq900
    | exact resolve eq900 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq921 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq914
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq914
    | exact resolve eq914 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq922 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq21 eq915
    | exact resolve eq915 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq924 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq921
    | exact resolve eq921 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq925 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq922
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq922
    | exact resolve eq922 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq927 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq924
    | exact resolve eq924 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq928 : (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq925
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq925
    | exact resolve eq925 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq930 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq927
       have i₂ := eq144 x
       grind)
    | exact superpose eq144 eq927
    | exact resolve eq927 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq931 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq928
       have i₂ := eq144 sF0
       grind)
    | exact superpose eq144 eq928
    | exact resolve eq928 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq933 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq930
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq930
    | exact resolve eq930 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq934 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq931
    | exact resolve eq931 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq936 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq933
       have i₂ := eq56 sF2 sF2 sF2
       grind)
    | exact superpose eq56 eq933
    | exact resolve eq933 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq937 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq934
       have i₂ := eq56 sF1 sF1 sF1
       grind)
    | exact superpose eq56 eq934
    | exact resolve eq934 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq2743 : (σ (k (M.op (M.op x y) (M.op x y)) y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq21 eq236
    | (have j0 := eq236 (M.op x y)
       grind)
    | exact resolve eq236 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq2752 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq766 eq2743
    | exact resolve eq2743 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743
  have eq2768 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq21 eq2752
    | exact resolve eq2752 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752
  have eq12671 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq936 eq56
    | exact resolve eq56 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq13453 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq937 eq56
    | exact resolve eq56 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq14824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13453 eq12671
    | exact resolve eq12671 eq13453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13453
  have eq14838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq14824
    | exact resolve eq14824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14824
  have eq14840 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq14838
       have r₂ := eq28
       grind)
    | exact resolve eq14838 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14838
  have eq14874 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14840 eq767
    | exact resolve eq767 eq14840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14840
  have eq14880 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14874
       have i₂ := eq106 sF1
       grind)
    | exact superpose eq106 eq14874
    | exact resolve eq14874 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14874
  have eq14951 : (τ (σ y)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14880 eq274
    | exact resolve eq274 eq14880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq14968 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14880
  have eq14979 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38 eq14951
    | exact resolve eq14951 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14951
  have eq14996 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq40 eq14979
    | exact resolve eq14979 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14979
  have eq15122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14996 eq937
    | exact resolve eq937 eq14996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937 eq14996
  have eq15160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq15122
  have eq15182 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq15160
    | exact resolve eq15160 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15160
  have eq15188 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15182
       have r₂ := eq28
       grind)
    | exact resolve eq15182 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15182
  have eq15197 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15188 eq144
    | exact resolve eq144 eq15188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15188
  have eq15223 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq15197
    | exact resolve eq15197 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15197
  have eq15226 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15223
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15223
    | exact resolve eq15223 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15223
  have eq15273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15226 eq12671
    | exact resolve eq12671 eq15226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq15273
  have eq15313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq15298
    | exact resolve eq15298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298
  have eq15327 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15313
       have r₂ := eq28
       grind)
    | exact resolve eq15313 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15313
  have eq16139 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15327 eq767
    | exact resolve eq767 eq15327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15327
  have eq16145 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16139
       have i₂ := eq106 sF1
       grind)
    | exact superpose eq106 eq16139
    | exact resolve eq16139 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16139
  have eq16164 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq16145
       have r₂ := eq14968
       grind)
    | exact resolve eq16145 eq14968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14968 eq16145
  have eq16184 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16164 eq15226
    | exact resolve eq15226 eq16164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15226
  have eq16185 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16164 eq12671
    | exact resolve eq12671 eq16164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16164
  have eq16210 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq16185
  have eq16211 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq16184
  have eq16241 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16211 eq27
    | exact resolve eq27 eq16211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16245 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16211 eq40
    | exact resolve eq40 eq16211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16211
  have eq16301 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq39 eq16245
    | exact resolve eq16245 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16245
  have eq16310 : y = (τ (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16301 eq40
    | exact resolve eq40 eq16301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16301
  have eq16357 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq16310
    | exact resolve eq16310 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16310
  have eq16365 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq16357 eq39
    | exact resolve eq39 eq16357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16357
  have eq16413 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq16365
    | exact resolve eq16365 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16365
  have eq16624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16241 eq16210
    | exact resolve eq16210 eq16241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16210 eq16241
  have eq16652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq16624
  have eq16671 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq16652
       have r₂ := eq28
       grind)
    | exact resolve eq16652 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16652
  have eq16682 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16671 eq40
    | exact resolve eq40 eq16671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq16671
  have eq16729 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq16682
    | exact resolve eq16682 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16682
  have eq16737 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16729 eq39
    | exact resolve eq39 eq16729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16729
  have eq16785 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq16737
    | exact resolve eq16737 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16737
  have eq16789 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16785 eq21
    | exact resolve eq21 eq16785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16791 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16785 eq96
    | exact resolve eq96 eq16785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq16816 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq16785
  have eq16817 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16789
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16789
    | exact resolve eq16789 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16789
  have eq18206 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16791 (M.op x y)
       have i₂ := eq16791 x
       grind)
    | exact superpose eq16791 eq16791
    | exact resolve eq16791 eq16791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16791
  have eq18222 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq18206
  have eq18995 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq144 y
       have i₂ := eq18222
       grind)
    | exact superpose eq18222 eq144
    | exact resolve eq144 eq18222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18222
  have eq19022 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18995
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18995
    | exact resolve eq18995 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18995
  have eq19025 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16817 eq19022
    | exact resolve eq19022 eq16817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16817 eq19022
  have eq19075 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq19025
  have eq19133 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19075 eq2768
    | exact resolve eq2768 eq19075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq19199 : (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35 eq19133
    | exact resolve eq19133 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq19133
  have eq19335 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq16413 eq19199
    | exact resolve eq19199 eq16413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16413 eq19199
  have eq19383 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq19335
  have eq19416 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19383
       have r₂ := eq16816
       grind)
    | exact resolve eq19383 eq16816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16816 eq19383
  have eq19419 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19416
       have i₂ := eq106 y
       grind)
    | exact superpose eq106 eq19416
    | exact resolve eq19416 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19416
  have eq19421 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19419
       have i₂ := eq144 y
       grind)
    | exact superpose eq144 eq19419
    | exact resolve eq19419 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19419
  have eq19423 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19421
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19421
    | exact resolve eq19421 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq19421
  have eq19464 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19423 eq767
    | exact resolve eq767 eq19423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19423
  have eq19474 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19464
       have i₂ := eq106 sF1
       grind)
    | exact superpose eq106 eq19464
    | exact resolve eq19464 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19464
  have eq19532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19474 eq12671
    | exact resolve eq12671 eq19474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12671 eq19474
  have eq19573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq19532
    | exact resolve eq19532 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19532
  have eq19587 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19573
       have r₂ := eq28
       grind)
    | exact resolve eq19573 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19573
  have eq38088 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19587 eq767
    | exact resolve eq767 eq19587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq19587
  have eq38096 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38088
       have i₂ := eq106 sF1
       grind)
    | exact superpose eq106 eq38088
    | exact resolve eq38088 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq38088
  have eq39400 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38096 eq19075
    | exact resolve eq19075 eq38096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19075 eq38096
  have eq39465 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq39400
  have eq39499 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39465 eq39
    | exact resolve eq39 eq39465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq39465
  have eq39553 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq39499
    | exact resolve eq39499 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq39499
  have eq39554 : x = (M.op x y) := by grind
  clear eq39553
  have eq39559 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq39554 eq21
    | exact resolve eq21 eq39554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq39567 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq39554 eq92
    | exact resolve eq92 eq39554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq39625 : x = (k (M.op x x) y) := by
    first
    | exact superpose eq39554 eq766
    | exact resolve eq766 eq39554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq39554
  have eq43068 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq39559
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39559
    | exact resolve eq39559 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39559
  have eq43419 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq43068 eq23
    | exact resolve eq23 eq43068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq43420 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq43068 eq27
    | exact resolve eq27 eq43068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq43431 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq43068 eq140
    | exact resolve eq140 eq43068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq45406 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k x y)) := by
    first
    | exact superpose eq43068 eq43431
    | exact resolve eq43431 eq43068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43068 eq43431
  have eq45997 : x = (M.op x x) := by
    first
    | (have i₁ := eq39567 (M.op x x)
       have i₂ := eq39567 x
       grind)
    | exact superpose eq39567 eq39567
    | exact resolve eq39567 eq39567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39567
  have eq46057 : x = (k x y) := by
    first
    | (have i₁ := eq39625
       have i₂ := eq45997
       grind)
    | exact superpose eq45997 eq39625
    | exact resolve eq39625 eq45997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39625
  have eq46217 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq45406
       have i₂ := eq46057
       grind)
    | exact superpose eq46057 eq45406
    | exact resolve eq45406 eq46057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45406 eq46057
  have eq46243 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq46217
       have i₂ := eq43419
       grind)
    | exact superpose eq43419 eq46217
    | exact resolve eq46217 eq43419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46217
  have eq46244 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq46243
  have eq46604 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq144 x
       have i₂ := eq45997
       grind)
    | exact superpose eq45997 eq144
    | exact resolve eq144 eq45997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq45997
  have eq46656 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq46604
       have i₂ := eq43419
       grind)
    | exact superpose eq43419 eq46604
    | exact resolve eq46604 eq43419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43419 eq46604
  have eq46832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq46656 eq46244
    | exact resolve eq46244 eq46656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46244
  have eq46852 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq46832
       have r₂ := eq28
       grind)
    | exact resolve eq46832 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46832
  have eq47930 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq46852 eq43420
    | exact resolve eq43420 eq46852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43420 eq46852
  have eq47969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46656 eq47930
    | exact resolve eq47930 eq46656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46656 eq47930
  have eq48453 : False := by grind
  exact eq48453

/-- `Equation1506`: `x = (y ◇ x) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_y_y_pxy_Equation1506 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 (M.op X2 X0))) = X0 := by
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
  have eq47 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op X0 y))) := by
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
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X2 X0)) = (M.op X0 (M.op X3 (M.op X3 (M.op X2 (M.op X2 X0))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X2 X0)) (M.op x X0) X3
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op (M.op X3 X0) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X2 X0)) X1 (M.op X3 X0)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) X1 (M.op X2 X0)
       have i₂ := eq14 X0 X2 (M.op X2 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq66 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k x y) := by
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
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
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
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq109 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq16
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq104
  have eq210 : y = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ x)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op X1 (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq509 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X1) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X2 (M.op X3 (M.op (M.op X0 X1) X1))
       have i₂ := eq53 X1 X3 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X1) X1)) = (M.op X1 (M.op X3 (M.op X3 (M.op (M.op X2 (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X1) X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X3
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq49
    | exact resolve eq49 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) = (M.op (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X0 (M.op X0 X1)) X2 X1
       have i₂ := eq49 X1 X0 X2
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 (M.op X2 X0)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq636 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq637 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49 (M.op X0 X0) X0 X0
       have i₂ := eq49 X0 X0 X0
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq637 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq637
    | exact resolve eq637 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq645 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq643 X0
       grind)
    | exact superpose eq643 eq14
    | exact resolve eq14 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op x (M.op X0 (M.op X0 X1))) X2
       have i₂ := eq52 X1 x X0 X2
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq703 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X0 (M.op X0 X1))) (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X3 X1) X1) (M.op X4 (M.op X4 (M.op (M.op X2 (M.op X0 (M.op X0 X1))) (M.op X0 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op (M.op X3 X0) X0) (M.op X1 (M.op X2 (M.op X2 X0))) X3
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq49
    | exact resolve eq49 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq52
  have eq756 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X1)) (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) X2 (σ X0)
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq14
    | (have j1 := eq72 X0 X1
       grind)
    | exact resolve eq14 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq786 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (M.op X1 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq635 eq635
    | exact resolve eq635 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq948 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq786 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq786
    | (have j0 := eq786 X0 x
       grind)
    | exact resolve eq786 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq1011 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq643 y
       have i₂ := eq948 y
       grind)
    | exact superpose eq948 eq643
    | exact resolve eq643 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1081 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq218 eq233
    | exact resolve eq233 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq1097 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq636 eq1081
    | exact resolve eq1081 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq1100 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq1081 eq219
    | exact resolve eq219 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq1081
  have eq1137 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1097 eq643
    | exact resolve eq643 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1142 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq1097 eq645
    | exact resolve eq645 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1226 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq633 X1 X2 x
       have i₂ := eq633 X1 X0 x
       grind)
    | exact superpose eq633 eq633
    | exact resolve eq633 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1350 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1100 eq1142
    | exact resolve eq1142 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100 eq1142
  have eq1355 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1350 eq1097
    | exact resolve eq1097 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1480 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X0 X1
       have i₂ := eq645 X0 X0
       grind)
    | exact superpose eq645 eq699
    | exact resolve eq699 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1499 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X3 X1) X1)) = (M.op (M.op X2 X1) (M.op (M.op X0 (M.op X0 X1)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq633 X1 (M.op X2 X1) X3
       have i₂ := eq699 X0 X1 X2
       grind)
    | exact superpose eq699 eq633
    | exact resolve eq633 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq699
  have eq1724 : (M.op y (M.op x (M.op x y))) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq210 eq1480
    | exact resolve eq1480 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq1734 : (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq218 eq1480
    | exact resolve eq1480 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1786 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1137 eq1734
    | exact resolve eq1734 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1792 : y = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq1011 eq1724
    | exact resolve eq1724 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011 eq1724
  have eq1859 : (σ y) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by grind
  clear eq1786
  have eq1901 : y = (k (M.op x (M.op x y)) y) := by grind
  clear eq1792
  have eq2410 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1226 X1 (M.op X0 X0) X0
       have i₂ := eq643 X0
       grind)
    | exact superpose eq643 eq1226
    | exact resolve eq1226 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2470 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq218 eq1226
    | exact resolve eq1226 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq2491 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq643 X1
       have i₂ := eq1226 X0 X1 X1
       grind)
    | (have i₁ := eq643 X1
       have i₂ := eq1226 X1 X1 X0
       grind)
    | exact superpose eq1226 eq643
    | exact resolve eq643 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq2513 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq645 X1 X1
       have i₂ := eq1226 X0 X1 X1
       grind)
    | (have i₁ := eq645 X1 X1
       have i₂ := eq1226 X1 X1 X0
       grind)
    | exact superpose eq1226 eq645
    | exact resolve eq645 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2611 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1350 eq2470
    | exact resolve eq2470 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq2470
  have eq4326 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509 X0 X1 X2 x
       have i₂ := eq1480 (M.op (M.op X0 X1) X1) x
       grind)
    | exact superpose eq1480 eq509
    | exact resolve eq509 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq4327 : ∀ X1 X2 : G, (M.op (M.op X2 X1) (M.op (M.op X1 X1) (M.op X1 X1))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq4326 X1 x X2
       have i₂ := eq1480 x X1
       grind)
    | exact superpose eq1480 eq4326
    | exact resolve eq4326 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4326
  have eq5893 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq632 X0 X1 X2
       have i₂ := eq2491 X0 X1
       grind)
    | exact superpose eq2491 eq632
    | exact resolve eq632 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq2491
  have eq5894 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5893 X0 X1 X2
       have i₂ := eq2513 X0 X1
       grind)
    | exact superpose eq2513 eq5893
    | exact resolve eq5893 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5893
  have eq6003 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5894 X1 (M.op X1 X0) X1
       have i₂ := eq5894 X1 X0 X1
       grind)
    | exact superpose eq5894 eq5894
    | exact resolve eq5894 eq5894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6005 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq2611 eq5894
    | exact resolve eq5894 eq2611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611
  have eq6433 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq6005 eq2410
    | exact resolve eq2410 eq6005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6005
  have eq6469 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6433 eq645
    | exact resolve eq645 eq6433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq6511 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq6469 eq2410
    | exact resolve eq2410 eq6469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6469
  have eq7507 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq6511 sF3
       have i₂ := eq1226 X0 sF4 sF3
       grind)
    | (have i₁ := eq6511 sF3
       have i₂ := eq1226 sF3 sF4 x
       grind)
    | exact superpose eq1226 eq6511
    | exact resolve eq6511 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq6511
  have eq11568 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq756 y y X0
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq756
    | (have j0 := eq756 y y x
       grind)
    | exact resolve eq756 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq756
  have eq11604 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq11568 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11568
  have eq11631 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11604 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11604
    | (have j0 := eq11604 X0
       grind)
    | exact resolve eq11604 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11604
  have eq11682 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11631 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11631
    | (have j0 := eq11631 X0
       grind)
    | exact resolve eq11631 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11631
  have eq11968 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op X1 (M.op X3 (M.op X3 (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq621 X0 X1 X1 X3
       have i₂ := eq1480 (M.op (M.op X0 X1) X1) X1
       grind)
    | exact superpose eq1480 eq621
    | exact resolve eq621 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq11969 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11968 X0 X1 x
       have i₂ := eq2410 (M.op (M.op X0 X1) X1) x
       grind)
    | exact superpose eq2410 eq11968
    | exact resolve eq11968 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11968
  have eq11970 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq11969 X1 x
       have i₂ := eq1480 x X1
       grind)
    | exact superpose eq1480 eq11969
    | exact resolve eq11969 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11969
  have eq13698 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X3 X1) X1) (M.op X4 (M.op X4 (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)))))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq703 X0 X1 X1 X3 X4
       have i₂ := eq1480 (M.op X0 (M.op X0 X1)) X1
       grind)
    | exact superpose eq1480 eq703
    | exact resolve eq703 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq13699 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X3 X1) X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq13698 X0 X1 X3 x
       have i₂ := eq2410 (M.op X0 (M.op X0 X1)) x
       grind)
    | exact superpose eq2410 eq13698
    | exact resolve eq13698 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410 eq13698
  have eq13700 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13699 X0 X1 x
       have i₂ := eq14 X1 (M.op x X1) X0
       grind)
    | exact superpose eq14 eq13699
    | exact resolve eq13699 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13699
  have eq25987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25987
    | exact resolve eq25987 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25987
  have eq26001 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq25996
       have r₂ := eq28
       grind)
    | exact resolve eq25996 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25996
  have eq26003 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq26001
    | exact resolve eq26001 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26001
  have eq26005 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq26003
  have eq26094 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26005 eq61
    | exact resolve eq61 eq26005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq26005
  have eq26109 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq26094
    | exact resolve eq26094 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26094
  have eq26112 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq26109
       have r₂ := eq66
       grind)
    | exact resolve eq26109 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq26109
  have eq26244 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq26112
       grind)
    | exact superpose eq26112 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq26112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26250 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq761 x y
       have i₂ := eq26112
       grind)
    | exact superpose eq26112 eq761
    | (have j0 := eq761 x y
       grind)
    | exact resolve eq761 eq26112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26112
  have eq26253 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq26250
  have eq26254 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26244
  have eq26257 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26253
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26253
    | exact resolve eq26253 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26253
  have eq26260 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26254
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26254
    | exact resolve eq26254 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26254
  have eq26270 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26257
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26257
    | exact resolve eq26257 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26257
  have eq26274 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq26270
    | exact resolve eq26270 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26270
  have eq26275 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq26274
  have eq26279 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26275
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26275
    | exact resolve eq26275 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26275
  have eq26282 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26279
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26279
    | exact resolve eq26279 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26279
  have eq26293 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq26303 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11970 x
       have i₂ := eq26260
       grind)
    | exact superpose eq26260 eq11970
    | exact resolve eq11970 eq26260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26260
  have eq26360 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26303
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26303
    | exact resolve eq26303 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26303
  have eq26513 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq761 x y
       have i₂ := eq26293
       grind)
    | exact superpose eq26293 eq761
    | (have j0 := eq761 x y
       grind)
    | exact resolve eq761 eq26293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26293
  have eq26516 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26513
  have eq26520 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26516
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26516
    | exact resolve eq26516 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26516
  have eq26531 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26520
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26520
    | exact resolve eq26520 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26520
  have eq26535 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq26531
    | exact resolve eq26531 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26531
  have eq26536 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq26535
  have eq26540 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26536
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26536
    | exact resolve eq26536 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26536
  have eq26543 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26540
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26540
    | exact resolve eq26540 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26540
  have eq27182 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq26360
       grind)
    | exact superpose eq26360 eq110
    | exact resolve eq110 eq26360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq26360
  have eq27239 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27182
  have eq27245 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq27239
    | exact resolve eq27239 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27239
  have eq27492 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26543 eq11970
    | exact resolve eq11970 eq26543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11970 eq26543
  have eq27549 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq27492
    | exact resolve eq27492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27492
  have eq29128 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26282 eq5894
    | exact resolve eq5894 eq26282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5894 eq26282
  have eq29152 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq27 eq29128
    | (have j0 := eq29128 X0
       grind)
    | exact resolve eq29128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29128
  have eq54112 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27549 eq11682
    | (have j0 := eq11682 (σ x)
       grind)
    | exact resolve eq11682 eq27549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11682
  have eq54157 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq54112
  have eq79497 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27245 eq54157
    | exact resolve eq54157 eq27245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27245 eq54157
  have eq79542 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq79497
  have eq79928 : (M.op (σ y) (σ (M.op x y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79542 eq13700
    | exact resolve eq13700 eq79542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79542
  have eq79941 : (M.op (σ y) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79928
       have i₂ := eq6003 sF3 sF4
       grind)
    | exact superpose eq6003 eq79928
    | exact resolve eq79928 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79928
  have eq79977 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1355 eq79941
    | exact resolve eq79941 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355 eq79941
  have eq80056 : (σ (M.op x y)) = (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79977 eq13700
    | exact resolve eq13700 eq79977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79977
  have eq80069 : (σ (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq80056
       have i₂ := eq6003 (M.op sF2 sF4) sF3
       grind)
    | exact superpose eq6003 eq80056
    | exact resolve eq80056 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80056
  have eq80098 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq80069
       have i₂ := eq6003 sF4 sF2
       grind)
    | exact superpose eq6003 eq80069
    | exact resolve eq80069 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80069
  have eq80113 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6433 eq80098
    | exact resolve eq80098 eq6433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6433 eq80098
  have eq80513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq80113 eq27549
    | exact resolve eq27549 eq80113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27549 eq80113
  have eq80606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq80513
  have eq80638 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq80606
       have r₂ := eq28
       grind)
    | exact resolve eq80606 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80606
  have eq80652 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq80638 eq28
    | exact resolve eq28 eq80638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80655 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq80638 eq67
    | (have r₁ := eq67
       have r₂ := eq80638
       grind)
    | exact resolve eq67 eq80638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq80670 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq80638 eq1859
    | exact resolve eq1859 eq80638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq80703 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq80655
  have eq80719 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq80670
    | exact resolve eq80670 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80670
  have eq81012 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq80638 eq80719
    | exact resolve eq80719 eq80638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80638 eq80719
  have eq81026 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq81012
  have eq82209 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq81026 eq109
    | exact resolve eq109 eq81026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq81026
  have eq82270 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq82209
    | exact resolve eq82209 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq82209
  have eq84638 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq82270
       grind)
    | exact superpose eq82270 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq82270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82270
  have eq84656 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq84638
  have eq121913 : ∀ X1 X2 X3 : G, (M.op X1 (M.op (M.op X3 X1) X1)) = (M.op (M.op X2 X1) (M.op X1 X1)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1499 x X1 X2 X3
       have i₂ := eq2513 x X1
       grind)
    | exact superpose eq2513 eq1499
    | exact resolve eq1499 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499 eq2513
  have eq121914 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X1) (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq121913 X1 X2 x
       have i₂ := eq1480 X1 x
       grind)
    | exact superpose eq1480 eq121913
    | exact resolve eq121913 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480 eq121913
  have eq172442 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq80703 eq88
    | exact resolve eq88 eq80703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80703
  have eq172468 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq172442
  have eq172474 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq172468
       have r₂ := eq80652
       grind)
    | exact resolve eq172468 eq80652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172468
  have eq174215 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq172474
  have eq174603 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq174215 eq88
    | exact resolve eq88 eq174215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq174215
  have eq174624 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq174603
  have eq174627 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq174624
       have r₂ := eq80652
       grind)
    | exact resolve eq174624 eq80652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80652 eq174624
  have eq174741 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq121914 x x
       have i₂ := eq174627
       grind)
    | exact superpose eq174627 eq121914
    | exact resolve eq121914 eq174627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121914 eq174627
  have eq174777 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq174741
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq174741
    | exact resolve eq174741 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174741
  have eq175443 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84656
       have i₂ := eq174777
       grind)
    | exact superpose eq174777 eq84656
    | exact resolve eq84656 eq174777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84656 eq174777
  have eq175550 : y = (M.op x y) := by grind
  clear eq175443
  have eq175639 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq175550 eq21
    | exact resolve eq21 eq175550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq175723 : y = (k (M.op x y) y) := by
    first
    | exact superpose eq175550 eq1901
    | exact resolve eq1901 eq175550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq175911 : y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq175723
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq175723
    | exact resolve eq175723 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175723
  have eq175985 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq175639
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq175639
    | exact resolve eq175639 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175639
  have eq176002 : y = (k y y) := by
    first
    | exact superpose eq175550 eq175911
    | exact resolve eq175911 eq175550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175911
  have eq176047 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq175985 eq27
    | exact resolve eq27 eq175985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq176079 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq175985 eq1137
    | exact resolve eq1137 eq175985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq176414 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq761 y y
       have i₂ := eq176002
       grind)
    | exact superpose eq176002 eq761
    | (have j0 := eq761 y y
       grind)
    | exact resolve eq761 eq176002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq176002
  have eq176421 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq176414
  have eq176422 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq176421
  have eq176437 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq176422
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq176422
    | exact resolve eq176422 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176422
  have eq176458 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq175985 eq176437
    | exact resolve eq176437 eq175985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176437
  have eq180021 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq176079 eq13700
    | exact resolve eq13700 eq176079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13700 eq176079
  have eq180040 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq180021
       have i₂ := eq6003 sF1 sF1
       grind)
    | exact superpose eq6003 eq180021
    | exact resolve eq180021 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003 eq180021
  have eq180093 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq176458 eq180040
    | exact resolve eq180040 eq176458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180040
  have eq180137 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq176458 eq180093
    | exact resolve eq180093 eq176458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176458 eq180093
  have eq180265 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq180137 eq7507
    | exact resolve eq7507 eq180137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7507
  have eq180282 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq180137 eq29152
    | exact resolve eq29152 eq180137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29152
  have eq180396 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq176047 eq180282
    | exact resolve eq180282 eq176047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180282
  have eq180397 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq180396
  have eq180403 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq176047 eq180265
    | exact resolve eq180265 eq176047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176047 eq180265
  have eq180464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq175985 eq180397
    | exact resolve eq180397 eq175985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180397
  have eq180466 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq175985 eq180403
    | exact resolve eq180403 eq175985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180403
  have eq180507 : y = (M.op x x) := by
    first
    | (have r₁ := eq180464
       have r₂ := eq28
       grind)
    | exact resolve eq180464 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180464
  have eq181039 : x = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq4327 x x
       have i₂ := eq180507
       grind)
    | exact superpose eq180507 eq4327
    | exact resolve eq4327 eq180507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4327 eq180507
  have eq181093 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq181039
       have i₂ := eq948 y
       grind)
    | exact superpose eq948 eq181039
    | exact resolve eq181039 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948 eq181039
  have eq181139 : x = (M.op x y) := by
    first
    | exact superpose eq175550 eq181093
    | exact resolve eq181093 eq175550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181093
  have eq181180 : x = (M.op x y) := by
    first
    | (have i₁ := eq181139
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq181139
    | exact resolve eq181139 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq181139
  have eq181205 : x = y := by
    first
    | exact superpose eq175550 eq181180
    | exact resolve eq181180 eq175550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175550 eq181180
  have eq181366 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq181205
       grind)
    | exact superpose eq181205 eq25
    | exact resolve eq25 eq181205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq181205
  have eq181891 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq175985 eq181366
    | exact resolve eq181366 eq175985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175985 eq181366
  have eq182130 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq181891
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq181891
    | exact resolve eq181891 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq181891
  have eq182993 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq182130 eq180137
    | exact resolve eq180137 eq182130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180137 eq182130
  have eq182996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq180466 eq182993
    | exact resolve eq182993 eq180466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180466 eq182993
  have eq183063 : False := by grind
  exact eq183063

/-- `Equation258`: `x = ((x ◇ x) ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_x_pyx_Equation258 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law258 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law258.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq24 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq32 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq37 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq18 X0
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq18 X0
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq18 (M.op X0 X0)
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq49 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq59 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq26 (τ X0)
       grind)
    | exact superpose eq26 eq19
    | exact resolve eq19 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq71 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq83 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71
    | exact resolve eq71 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq90 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 (k (τ X0) X1) X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq36
    | exact resolve eq36 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 (k X1 (τ X0)) X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq36
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq146 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq33 X0 (τ (M.op (σ (σ X0)) (σ (σ X0))))
       have i₂ := eq83 (σ X0)
       grind)
    | exact superpose eq83 eq33
    | exact resolve eq33 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq154 : ∀ X0 : G, (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq146 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq146
    | exact resolve eq146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq198 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq62 (τ X0)
       grind)
    | exact superpose eq62 eq19
    | exact resolve eq19 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq198 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq198
    | exact resolve eq198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq371 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq37 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq372 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq376 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq372
    | (have j0 := eq372 X0
       grind)
    | exact resolve eq372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq469 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) (σ (k X0 X0))) (M.op (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq50
    | (have j1 := eq36 X0 X0
       grind)
    | exact resolve eq50 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq473 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq9
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) (σ (k X0 X0))) (M.op (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq469 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq843 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq90 X0 X1 X2
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq90 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq90 X0 X1 X2
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq843 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq845 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq844 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq846 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq845 X0 X1 X2
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq845
    | (have j0 := eq845 X0 X1 X2
       grind)
    | exact resolve eq845 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq845
  have eq893 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq91 X0 X1 X2
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq91 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq91 X0 X1 X2
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq893 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq895 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq894 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq896 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq895 X0 X1 X2
       have i₂ := eq32 X0 X1 X2
       grind)
    | exact superpose eq32 eq895
    | (have j0 := eq895 X0 X1 X2
       grind)
    | exact resolve eq895 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq895
  have eq1223 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq26
    | (have j1 := eq376 X0
       grind)
    | exact resolve eq26 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq376
  have eq1234 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1223 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1223
    | (have j0 := eq1223 X0
       grind)
    | exact resolve eq1223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq2126 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq1234 X0
       grind)
    | exact superpose eq1234 eq10
    | (have j1 := eq1234 X0
       grind)
    | exact resolve eq10 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq2552 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2126 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2126
    | (have j0 := eq2126 (σ X0)
       grind)
    | exact resolve eq2126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq2609 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2552 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq2552
    | (have j0 := eq2552 X0
       grind)
    | exact resolve eq2552 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2552
  have eq2621 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2609 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2609
    | (have j0 := eq2609 X0
       grind)
    | exact resolve eq2609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2609
  have eq2625 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2621 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2621
    | (have j0 := eq2621 X0
       grind)
    | exact resolve eq2621 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621
  have eq2645 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq2625 X0
       grind)
    | exact superpose eq2625 eq10
    | (have j1 := eq2625 X0
       grind)
    | exact resolve eq10 eq2625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2625
  have eq2691 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2645 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2645
    | (have j0 := eq2645 X0
       grind)
    | exact resolve eq2645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq2778 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2691
  have eq2904 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq43 X0 (σ X0)
       grind)
    | exact superpose eq43 eq51
    | (have j1 := eq43 X0 (σ X0)
       grind)
    | exact resolve eq51 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq51
  have eq2914 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq2904 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq2919 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq2914 X0
       have j1 := eq2778 (σ X0)
       grind)
    | (have r₁ := eq2914 X0
       have r₂ := eq2778 (σ X0)
       grind)
    | exact resolve eq2914 eq2778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778 eq2914
  have eq2932 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq2919 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2919
    | (have j0 := eq2919 X0
       grind)
    | exact resolve eq2919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq2938 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2932 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2932
    | (have j0 := eq2932 X0
       grind)
    | exact resolve eq2932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932
  have eq4143 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0
       have i₂ := eq473 X0 X1
       grind)
    | exact superpose eq473 eq50
    | exact resolve eq50 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4145 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq473 X0 X1
       grind)
    | exact superpose eq473 eq9
    | exact resolve eq9 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4146 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2
       have i₂ := eq473 X0 X1
       grind)
    | exact superpose eq473 eq9
    | exact resolve eq9 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq8869 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq846 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq8870 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq8869 X0 X1 X2
       have j1 := eq90 X0 X1 X2
       grind)
    | (have r₁ := eq8869 X0 X1 X2
       have r₂ := eq90 X0 X1 X2
       grind)
    | exact resolve eq8869 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq8869
  have eq9262 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq896 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq9263 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq9262 X0 X1 X2
       have j1 := eq91 X0 X1 X2
       grind)
    | (have r₁ := eq9262 X0 X1 X2
       have r₂ := eq91 X0 X1 X2
       grind)
    | exact resolve eq9262 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq9262
  have eq12111 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ (k X0 X0))
       have i₂ := eq476 X0
       grind)
    | exact superpose eq476 eq50
    | (have j1 := eq476 X0
       grind)
    | exact resolve eq50 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq13721 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq2938 X0
       grind)
    | exact superpose eq2938 eq11
    | (have j1 := eq2938 X0
       grind)
    | exact resolve eq11 eq2938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq61729 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))))) ∨ (σ X1) = (M.op (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq8870 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))) X1
       have i₂ := eq62 (τ X0)
       grind)
    | exact superpose eq62 eq8870
    | (have j0 := eq8870 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))) X1
       grind)
    | exact resolve eq8870 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq8870
  have eq62187 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq61729 X0 X1
       have i₂ := eq203 X0
       grind)
    | exact superpose eq203 eq61729
    | (have j0 := eq61729 X0 X1
       grind)
    | exact resolve eq61729 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61729
  have eq62360 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq62187 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq62187
    | (have j0 := eq62187 X0 X1
       grind)
    | exact resolve eq62187 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62187
  have eq62496 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62360 X0 X1
       have i₂ := eq203 X0
       grind)
    | exact superpose eq203 eq62360
    | (have j0 := eq62360 X0 X1
       grind)
    | exact resolve eq62360 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq62360
  have eq62713 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (k (σ X0) (τ (M.op (σ (σ X0)) (σ (σ X0)))))) ∨ (σ X1) = (M.op (k (σ X0) (τ (M.op (σ (σ X0)) (σ (σ X0))))) (k (σ X0) (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9263 X0 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X1
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq9263
    | (have j0 := eq9263 X0 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X1
       grind)
    | exact resolve eq9263 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq9263
  have eq63202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (k (σ X0) (τ (M.op (σ (σ X0)) (σ (σ X0))))) (k (σ X0) (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq62713 X0 X1
       have i₂ := eq83 (σ X0)
       grind)
    | exact superpose eq83 eq62713
    | (have j0 := eq62713 X0 X1
       grind)
    | exact resolve eq62713 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62713
  have eq63353 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63202 X0 X1
       have i₂ := eq83 (σ X0)
       grind)
    | exact superpose eq83 eq63202
    | (have j0 := eq63202 X0 X1
       grind)
    | exact resolve eq63202 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq63202
  have eq69622 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62496 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62496
    | exact resolve eq62496 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62496
  have eq215239 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12111 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12111
  have eq215256 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq215239 X0
       have j1 := eq13721 X0
       grind)
    | (have r₁ := eq215239 X0
       have r₂ := eq13721 X0
       grind)
    | exact resolve eq215239 eq13721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13721 eq215239
  have eq215375 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq215256 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215256
    | exact resolve eq215256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215616 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq215256 X0
       grind)
    | exact superpose eq215256 eq9
    | exact resolve eq9 eq215256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215618 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18 (σ X0)
       have i₂ := eq215256 X0
       grind)
    | exact superpose eq215256 eq18
    | exact resolve eq18 eq215256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq215645 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op (σ X0) X1) X1) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4145 (σ X0) X1
       have i₂ := eq215256 X0
       grind)
    | exact superpose eq215256 eq4145
    | exact resolve eq4145 eq215256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215999 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq215375 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq215375
    | exact resolve eq215375 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq215375
  have eq216115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq215999 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215999
    | exact resolve eq215999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215999
  have eq220048 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq215616 X0 X1
       have i₂ := eq216115 X0
       grind)
    | exact superpose eq216115 eq215616
    | exact resolve eq215616 eq216115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215616
  have eq220076 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X1)) = (M.op (M.op (σ X0) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220048 (M.op (M.op X0 X1) X1) X2
       have i₂ := eq4143 X0 X1
       grind)
    | exact superpose eq4143 eq220048
    | exact resolve eq220048 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223369 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq215618 X0
       have i₂ := eq216115 X0
       grind)
    | exact superpose eq216115 eq215618
    | exact resolve eq215618 eq216115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215618
  have eq223521 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X1) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq223369 (M.op (M.op X0 X1) X1)
       have i₂ := eq4143 X0 X1
       grind)
    | exact superpose eq4143 eq223369
    | exact resolve eq223369 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223369
  have eq224867 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) X1)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ (M.op (M.op X0 X1) X1)) (σ (M.op (M.op X0 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4145 (σ (M.op (M.op X0 X1) X1)) (σ X0)
       have i₂ := eq223521 X0 X1
       grind)
    | exact superpose eq223521 eq4145
    | exact resolve eq4145 eq223521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4145
  have eq224930 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) X1)) = (M.op (M.op (σ X0) (σ X0)) (σ (k (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq224867 X0 X1
       have i₂ := eq215256 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq215256 eq224867
    | exact resolve eq224867 eq215256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224867
  have eq225237 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) X1)) = (M.op (M.op (σ X0) (σ X0)) (σ (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq224930 X0 X1
       have i₂ := eq216115 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq216115 eq224930
    | exact resolve eq224930 eq216115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224930
  have eq225462 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq225237 X0 X1
       have i₂ := eq4143 X0 X1
       grind)
    | exact superpose eq4143 eq225237
    | exact resolve eq225237 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143 eq225237
  have eq225587 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq225462 X0 X1
       have i₂ := eq215256 X0
       grind)
    | exact superpose eq215256 eq225462
    | exact resolve eq225462 eq215256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225462
  have eq225666 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq225587 X0 X1
       have i₂ := eq216115 X0
       grind)
    | exact superpose eq216115 eq225587
    | exact resolve eq225587 eq216115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225587
  have eq235736 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (τ (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op (M.op X0 X2) X2)
       have i₂ := eq220076 X0 X2 X1
       grind)
    | exact superpose eq220076 eq10
    | exact resolve eq10 eq220076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220076
  have eq245308 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq235736 (M.op (M.op X0 X1) X1) (σ X0) X2
       have i₂ := eq223521 X0 X1
       grind)
    | exact superpose eq223521 eq235736
    | exact resolve eq235736 eq223521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223521 eq235736
  have eq246276 : ∀ X0 X1 X2 : G, (τ (σ (k X0 X0))) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq245308 X0 X1 X2
       have i₂ := eq215256 X0
       grind)
    | exact superpose eq215256 eq245308
    | exact resolve eq245308 eq215256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245308
  have eq246786 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq246276 X0 X1 X2
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq246276
    | exact resolve eq246276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246276
  have eq261902 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4146 (M.op X0 X1) X1 X1
       have i₂ := eq246786 X0 X1 X1
       grind)
    | exact superpose eq246786 eq4146
    | exact resolve eq4146 eq246786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4146 eq246786
  have eq262169 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261902 X0 X1
       have i₂ := eq216115 X0
       grind)
    | exact superpose eq216115 eq261902
    | exact resolve eq261902 eq216115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261902
  have eq314672 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op (σ X0) X1) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq215645 X0 X1
       have i₂ := eq216115 X0
       grind)
    | exact superpose eq216115 eq215645
    | exact resolve eq215645 eq216115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215645
  have eq319438 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) X1) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq314672 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq314672
    | exact resolve eq314672 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq314672
  have eq319946 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq319438 X0 x
       have i₂ := eq220048 (M.op X0 X0) x
       grind)
    | exact superpose eq220048 eq319438
    | exact resolve eq319438 eq220048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220048 eq319438
  have eq320310 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq319946 X0
       have i₂ := eq262169 X0 X0
       grind)
    | exact superpose eq262169 eq319946
    | exact resolve eq319946 eq262169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262169 eq319946
  have eq2532330 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63353 X0 X1
       have i₂ := eq215256 X0
       grind)
    | exact superpose eq215256 eq63353
    | (have j0 := eq63353 X0 X1
       grind)
    | exact resolve eq63353 eq215256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63353 eq215256
  have eq2532331 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2532330 X0 X1
       have i₂ := eq216115 X0
       grind)
    | exact superpose eq216115 eq2532330
    | (have j0 := eq2532330 X0 X1
       grind)
    | exact resolve eq2532330 eq216115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216115 eq2532330
  have eq2533242 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2532331 y x
       grind)
    | exact superpose eq2532331 eq16
    | (have j1 := eq2532331 y x
       grind)
    | exact resolve eq16 eq2532331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532331
  have eq2541225 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2533242
       have i₂ := eq69622 x y
       grind)
    | exact superpose eq69622 eq2533242
    | (have j1 := eq69622 x y
       grind)
    | exact resolve eq2533242 eq69622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69622 eq2533242
  have eq2541236 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2541225
  have eq2541405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq320310 y
       have i₂ := eq2541236
       grind)
    | exact superpose eq2541236 eq320310
    | exact resolve eq320310 eq2541236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320310 eq2541236
  have eq2541756 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2541405
       have r₂ := eq16
       grind)
    | exact resolve eq2541405 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541405
  have eq2541968 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2541756
       grind)
    | exact superpose eq2541756 eq10
    | exact resolve eq10 eq2541756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541756
  have eq2542919 : x = (M.op y y) := by
    first
    | (have i₁ := eq2541968
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2541968
    | exact resolve eq2541968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541968
  have eq2543837 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq225666 y y
       have i₂ := eq2542919
       grind)
    | exact superpose eq2542919 eq225666
    | exact resolve eq225666 eq2542919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225666 eq2542919
  have eq2543957 : False := by grind
  exact eq2543957

/-- `Equation2670`: `x = ((x ◇ y) ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation2670 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2670 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2670.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
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
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq39
    | exact resolve eq39 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq39
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq25
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq88 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62 x y
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 x y
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq776 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq199
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq199
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq199
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq199
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq199 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq777 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq776
  have eq837 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq208 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq208
    | (have j0 := eq208 (τ X0) (τ X1)
       grind)
    | exact resolve eq208 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq849 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq837 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq837
    | (have j0 := eq837 X0 X1
       grind)
    | exact resolve eq837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq858 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq849 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq849
    | (have j0 := eq849 X0 X1
       grind)
    | exact resolve eq849 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq866 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq858 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq858
    | (have j0 := eq858 X0 X1
       grind)
    | exact resolve eq858 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq869 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq866 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq866
    | (have j0 := eq866 X0 X1
       grind)
    | exact resolve eq866 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq871 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq869 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq869
    | (have j0 := eq869 X0 X1
       grind)
    | exact resolve eq869 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq869
  have eq872 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq871 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq871
    | (have j0 := eq871 X0 X1
       grind)
    | exact resolve eq871 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq873 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq872 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq872
    | (have j0 := eq872 X0 X1
       grind)
    | exact resolve eq872 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq10300 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq777
       grind)
    | exact superpose eq777 eq16
    | exact resolve eq16 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq10301 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10300
       have r₂ := eq41 x
       grind)
    | exact resolve eq10300 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10300
  have eq10304 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq10301
       grind)
    | exact superpose eq10301 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq10301
       grind)
    | exact resolve eq12 eq10301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10301
  have eq10335 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq10304
  have eq10345 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq208 x y
       have i₂ := eq10335
       grind)
    | exact superpose eq10335 eq208
    | (have j0 := eq208 x y
       grind)
    | exact resolve eq208 eq10335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq10335
  have eq10362 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq10345
  have eq10363 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq10362
  have eq10451 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10363
       grind)
    | exact superpose eq10363 eq16
    | exact resolve eq16 eq10363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10458 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88 x (σ y)
       have i₂ := eq10363
       grind)
    | exact superpose eq10363 eq88
    | (have j0 := eq88 x (σ y)
       grind)
    | (have r₁ := eq88 x (σ y)
       have r₂ := eq10363
       grind)
    | exact resolve eq88 eq10363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq10363
  have eq10496 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq10458
  have eq10507 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10496
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq10496
    | exact resolve eq10496 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10496
  have eq10593 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10507
       grind)
    | exact superpose eq10507 eq10
    | exact resolve eq10 eq10507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10507
  have eq10664 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10593
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10593
    | exact resolve eq10593 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10593
  have eq10666 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10664
       grind)
    | exact superpose eq10664 eq16
    | exact resolve eq16 eq10664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10664
  have eq10667 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq10666
       have r₂ := eq41 x
       grind)
    | exact resolve eq10666 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10666
  have eq10773 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq10667
       grind)
    | exact superpose eq10667 eq10
    | exact resolve eq10 eq10667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10667
  have eq10846 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq10773
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq10773
    | exact resolve eq10773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10773
  have eq10860 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq873 x y
       have i₂ := eq10846
       grind)
    | exact superpose eq10846 eq873
    | (have j0 := eq873 x y
       grind)
    | (have r₁ := eq873 x y
       have r₂ := eq10846
       grind)
    | exact resolve eq873 eq10846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq10846
  have eq10874 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq10860
  have eq10978 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10874
       grind)
    | exact superpose eq10874 eq16
    | exact resolve eq16 eq10874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10874
  have eq10981 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq10978
       have r₂ := eq41 x
       grind)
    | exact resolve eq10978 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10978
  have eq10982 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10451
       have i₂ := eq10981
       grind)
    | exact superpose eq10981 eq10451
    | exact resolve eq10451 eq10981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10451
  have eq11017 : (σ x) = (σ y) := by grind
  clear eq10982
  have eq11238 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11017
       grind)
    | exact superpose eq11017 eq16
    | exact resolve eq16 eq11017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11017
  have eq11315 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11238
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq11238
    | exact resolve eq11238 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq11238
  have eq11316 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11315
       have i₂ := eq10981
       grind)
    | exact superpose eq10981 eq11315
    | exact resolve eq11315 eq10981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10981 eq11315
  have eq11317 : False := by grind
  exact eq11317

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq190 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq194 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq190 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq190 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq190 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq190 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq275 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq194 (σ X1) (σ X0)
       grind)
    | exact superpose eq194 eq15
    | (have j1 := eq194 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq194 (τ X1) X0
       grind)
    | exact superpose eq194 eq17
    | (have j1 := eq194 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq17 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq194
  have eq3814 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277
    | exact resolve eq277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq3922 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3814 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3814
    | (have j0 := eq3814 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq3814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814
  have eq10335 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275 x y
       grind)
    | exact superpose eq275 eq16
    | (have j1 := eq275 x y
       grind)
    | exact resolve eq16 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq10737 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10335
       have i₂ := eq3922 y x
       grind)
    | exact superpose eq3922 eq10335
    | (have j1 := eq3922 (σ x) (σ y)
       grind)
    | (have r₁ := eq10335
       have r₂ := eq3922 y x
       grind)
    | (have r₁ := eq10335
       have r₂ := eq3922 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10335
       have r₂ := eq3922 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10335 eq3922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922 eq10335
  have eq10738 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq10737
  have eq11065 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10738
       grind)
    | exact superpose eq10738 eq10
    | exact resolve eq10 eq10738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10738
  have eq11119 : x = y ∨ x = y := by
    first
    | (have i₁ := eq11065
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11065
    | exact resolve eq11065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11065
  have eq11120 : x = y := by grind
  clear eq11119
  have eq11318 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11120
       grind)
    | exact superpose eq11120 eq16
    | exact resolve eq16 eq11120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11120
  have eq11319 : False := by grind
  exact eq11319

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq23 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
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
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq38 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
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
  have eq82 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq21 X3 X2 X4 X0
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq21
  have eq108 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq37 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq170 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq13
    | (have j0 := eq13 X1 (τ X0)
       have j1 := eq38 X0 X1
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq38 X0 (τ X0)
       grind)
    | exact resolve eq13 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq377 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq378 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq368 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq379 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq378 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq381 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq377 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq377
    | (have j0 := eq377 X0
       grind)
    | exact resolve eq377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq1187 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1205 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1187 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1187
    | exact resolve eq1187 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq2121 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq82 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2161 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq2121 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq2121
    | exact resolve eq2121 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121
  have eq3552 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq10
    | (have j1 := eq381 X0
       grind)
    | exact resolve eq10 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq7420 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq379 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq379
    | exact resolve eq379 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq7504 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7420 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7420
    | (have j0 := eq7420 X0 X1
       grind)
    | exact resolve eq7420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7420
  have eq11092 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq3552 X0
       grind)
    | exact superpose eq3552 eq27
    | (have j1 := eq3552 X0
       grind)
    | exact resolve eq27 eq3552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq11151 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3552 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552
  have eq11176 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11092 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11092
    | (have j0 := eq11092 X0
       grind)
    | exact resolve eq11092 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11092
  have eq11357 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11176 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11176
    | (have j0 := eq11176 (σ X0)
       grind)
    | exact resolve eq11176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11176
  have eq11460 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11357 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq11357
    | (have j0 := eq11357 X0
       grind)
    | exact resolve eq11357 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11357
  have eq11468 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11460 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11460
    | (have j0 := eq11460 X0
       grind)
    | exact resolve eq11460 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11460
  have eq11473 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11468 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq11468
    | (have j0 := eq11468 X0
       grind)
    | exact resolve eq11468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11468
  have eq11668 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq11473 X0
       grind)
    | exact superpose eq11473 eq10
    | (have j1 := eq11473 X0
       grind)
    | exact resolve eq10 eq11473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11473
  have eq11747 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11668 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11668
    | (have j0 := eq11668 X0
       grind)
    | exact resolve eq11668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11668
  have eq15998 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq11151 (σ X0)
       have i₂ := eq34 X0 (σ X0)
       grind)
    | exact superpose eq34 eq11151
    | exact resolve eq11151 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq11151
  have eq16005 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15998 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15998
    | (have j0 := eq15998 X0
       grind)
    | exact resolve eq15998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15998
  have eq16008 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq16005 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16005
    | (have j0 := eq16005 X0
       grind)
    | exact resolve eq16005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16005
  have eq16011 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16008 X0
       have j1 := eq11747 X0
       grind)
    | (have r₁ := eq16008 X0
       have r₂ := eq11747 X0
       grind)
    | exact resolve eq16008 eq11747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11747 eq16008
  have eq16094 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq16011 (σ X0)
       grind)
    | exact superpose eq16011 eq15
    | exact resolve eq15 eq16011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16154 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16094 X0
       have i₂ := eq16011 X0
       grind)
    | exact superpose eq16011 eq16094
    | exact resolve eq16094 eq16011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16011 eq16094
  have eq16951 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq16154 X0
       grind)
    | exact superpose eq16154 eq54
    | exact resolve eq54 eq16154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96040 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq7504 (τ X0) X1
       grind)
    | exact superpose eq7504 eq19
    | (have j1 := eq7504 (τ X0) X1
       grind)
    | exact resolve eq19 eq7504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7504
  have eq96363 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96040 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96040
    | (have j0 := eq96040 X0 X1
       grind)
    | exact resolve eq96040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96040
  have eq96483 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96363 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq96363
    | (have j0 := eq96363 X0 X1
       grind)
    | exact resolve eq96363 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq96363
  have eq1159453 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96483 (σ X1) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq96483
    | (have j0 := eq96483 (σ X1) X0
       grind)
    | exact resolve eq96483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96483
  have eq1160488 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1159453 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1159453
    | (have j0 := eq1159453 X0 X1
       grind)
    | exact resolve eq1159453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159453
  have eq1160822 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1160488 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1160488
    | (have j0 := eq1160488 X0 X1
       grind)
    | exact resolve eq1160488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160488
  have eq1162136 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq1160822 y x
       grind)
    | exact superpose eq1160822 eq108
    | (have j1 := eq1160822 y x
       grind)
    | (have r₁ := eq108
       have r₂ := eq1160822 y x
       grind)
    | exact resolve eq108 eq1160822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1160822
  have eq1162719 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq1162136
  have eq1162781 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq117 x y
       grind)
    | (have r₁ := eq1162719
       have r₂ := eq117 x y
       grind)
    | exact resolve eq1162719 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1162719
  have eq1162966 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1162781
       have i₂ := eq16154 y
       grind)
    | exact superpose eq16154 eq1162781
    | exact resolve eq1162781 eq16154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162781
  have eq1168987 : (M.op y y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1162966
       grind)
    | exact superpose eq1162966 eq10
    | exact resolve eq10 eq1162966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162966
  have eq1169627 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1168987
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1168987
    | exact resolve eq1168987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168987
  have eq1169628 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1169627
  have eq1169654 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq1169628
       grind)
    | exact superpose eq1169628 eq54
    | exact resolve eq54 eq1169628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1169711 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16951 y
       have i₂ := eq1169628
       grind)
    | exact superpose eq1169628 eq16951
    | exact resolve eq16951 eq1169628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16951 eq1169628
  have eq1184496 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1169711
       grind)
    | exact superpose eq1169711 eq16
    | exact resolve eq16 eq1169711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169711
  have eq1187833 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1184496
       have i₂ := eq1169654
       grind)
    | exact superpose eq1169654 eq1184496
    | exact resolve eq1184496 eq1169654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169654 eq1184496
  have eq1187836 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1187833
  have eq1187837 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1187836
  have eq1187842 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1187837
       grind)
    | exact superpose eq1187837 eq16
    | exact resolve eq16 eq1187837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188094 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq1187837
       grind)
    | exact superpose eq1187837 eq9
    | exact resolve eq9 eq1187837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188242 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1205 (σ x) (σ y)
       have i₂ := eq1187837
       grind)
    | exact superpose eq1187837 eq1205
    | exact resolve eq1205 eq1187837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188993 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1188242
       have i₂ := eq16154 x
       grind)
    | exact superpose eq16154 eq1188242
    | exact resolve eq1188242 eq16154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16154 eq1188242
  have eq1189068 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1188094 X0
       have i₂ := eq1205 (σ x) X0
       grind)
    | (have i₁ := eq1188094 X0
       have i₂ := eq1205 (σ x) (M.op (σ x) X0)
       grind)
    | exact superpose eq1205 eq1188094
    | exact resolve eq1188094 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188094
  have eq1191542 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1188993
       grind)
    | exact superpose eq1188993 eq10
    | exact resolve eq10 eq1188993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188993
  have eq1192194 : x = (M.op x x) := by
    first
    | (have i₁ := eq1191542
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1191542
    | exact resolve eq1191542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191542
  have eq1193245 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq170 x X0
       have i₂ := eq1192194
       grind)
    | exact superpose eq1192194 eq170
    | exact resolve eq170 eq1192194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq1193987 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq2161 x x x
       have i₂ := eq1192194
       grind)
    | exact superpose eq1192194 eq2161
    | exact resolve eq2161 eq1192194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161 eq1192194
  have eq1194124 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1193987 X0
       have i₂ := eq1205 x X0
       grind)
    | (have i₁ := eq1193987 X0
       have i₂ := eq1205 x (M.op x X0)
       grind)
    | exact superpose eq1205 eq1193987
    | exact resolve eq1193987 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq1193987
  have eq1206811 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1193245 X0
       have i₂ := eq1194124 X0
       grind)
    | exact superpose eq1194124 eq1193245
    | exact resolve eq1193245 eq1194124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193245 eq1194124
  have eq1208595 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq1187842
       have i₂ := eq1206811 y
       grind)
    | exact superpose eq1206811 eq1187842
    | exact resolve eq1187842 eq1206811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187842 eq1206811
  have eq1629523 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1189068 (σ y)
       have i₂ := eq1187837
       grind)
    | exact superpose eq1187837 eq1189068
    | exact resolve eq1189068 eq1187837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189068
  have eq1631940 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1629523
       have i₂ := eq1187837
       grind)
    | exact superpose eq1187837 eq1629523
    | exact resolve eq1629523 eq1187837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187837 eq1629523
  have eq1632257 : False := by grind
  exact eq1632257
