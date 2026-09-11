import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxy_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq20 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq20 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq83 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq136 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq53 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq53 X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq53 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq139 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq136 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq307 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq395 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) ∨ (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq139 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq34 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq34 eq139
    | (have j0 := eq139 (M.op (M.op X0 X0) X0) X1
       grind)
    | exact resolve eq139 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq406 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq20 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq395 X0 X1
       have i₂ := eq20 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq20 eq395
    | (have j0 := eq395 X0 X1
       grind)
    | exact resolve eq395 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq407 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq406 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq650 : ∀ X0 X1 : G, (k (τ X0) (M.op (M.op X1 X1) X1)) = (τ (M.op X0 (σ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq407 X1 X0
       grind)
    | exact superpose eq407 eq31
    | exact resolve eq31 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq687 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (M.op X1 X1) X1)) = (τ (M.op X0 (σ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 X1
       have i₂ := eq34 X1 (τ X0)
       grind)
    | exact superpose eq34 eq650
    | exact resolve eq650 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq650
  have eq715 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 X1 X1
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq754 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq715
    | (have j0 := eq715 X0 X1
       grind)
    | exact resolve eq715 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq1354 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq83 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq83 X0
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1367 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq307
       have i₂ := eq754 y x
       grind)
    | exact superpose eq754 eq307
    | (have j1 := eq754 (σ x) (σ y)
       grind)
    | (have r₁ := eq307
       have r₂ := eq754 y x
       grind)
    | (have r₁ := eq307
       have r₂ := eq754 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq307
       have r₂ := eq754 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq307 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq754
  have eq1428 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq1427
  have eq4949 : ∀ X0 X1 : G, (τ (σ (M.op (M.op X0 X0) X0))) = (M.op (τ (M.op (M.op X1 X1) X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq687 (M.op (M.op X1 X1) X1) X0
       have i₂ := eq20 X1 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq20 eq687
    | exact resolve eq687 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq5031 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (τ (M.op (M.op X1 X1) X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4949 X0 X1
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq4949
    | exact resolve eq4949 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4949
  have eq6939 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (M.op (M.op X0 X0) X0)) (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0)))
       have i₂ := eq5031 (τ (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq5031 eq9
    | exact resolve eq9 eq5031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5031
  have eq6980 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6939 X0 X1
       have i₂ := eq20 (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))
       grind)
    | (have i₁ := eq6939 X0 X1
       have i₂ := eq20 X0 (M.op (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq20 eq6939
    | exact resolve eq6939 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6939
  have eq32054 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1367 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1367
    | exact resolve eq1367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq32262 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32054 X0 X1
       have i₂ := eq31 (σ X0) X0
       grind)
    | exact superpose eq31 eq32054
    | (have j0 := eq32054 X0 X1
       grind)
    | exact resolve eq32054 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq32054
  have eq32271 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32262 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32262
    | (have j0 := eq32262 X0 X0
       grind)
    | exact resolve eq32262 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32262
  have eq32641 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq32271 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32271
  have eq32642 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq32641 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32641
  have eq32835 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq138 X0
       have i₂ := eq32642 X0
       grind)
    | exact superpose eq32642 eq138
    | (have j0 := eq138 X0
       grind)
    | exact resolve eq138 eq32642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq32887 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32642 (σ X0)
       grind)
    | exact superpose eq32642 eq15
    | exact resolve eq15 eq32642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32960 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32887 X0
       have i₂ := eq32642 X0
       grind)
    | exact superpose eq32642 eq32887
    | exact resolve eq32887 eq32642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32642 eq32887
  have eq33961 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X1
       have i₂ := eq32960 X0
       grind)
    | exact superpose eq32960 eq20
    | exact resolve eq20 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq33996 : ∀ X0 X1 : G, (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6980 (σ X0) X1
       have i₂ := eq32960 X0
       grind)
    | exact superpose eq32960 eq6980
    | exact resolve eq6980 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6980
  have eq820109 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1428
       grind)
    | exact superpose eq1428 eq16
    | exact resolve eq16 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq820110 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq820109
       have r₂ := eq32960 x
       grind)
    | exact resolve eq820109 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820109
  have eq820111 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq820110
       have i₂ := eq32960 x
       grind)
    | exact superpose eq32960 eq820110
    | exact resolve eq820110 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820110
  have eq821869 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq820111
       grind)
    | exact superpose eq820111 eq10
    | exact resolve eq10 eq820111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820111
  have eq822311 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq821869
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq821869
    | exact resolve eq821869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821869
  have eq822450 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq822311
       grind)
    | exact superpose eq822311 eq16
    | exact resolve eq16 eq822311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822311
  have eq822454 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq822450
       have r₂ := eq32960 x
       grind)
    | exact resolve eq822450 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822450
  have eq826381 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq32835 x
       have i₂ := eq822454
       grind)
    | exact superpose eq822454 eq32835
    | (have j0 := eq32835 x
       grind)
    | (have r₁ := eq32835 x
       have r₂ := eq822454
       grind)
    | exact resolve eq32835 eq822454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822454
  have eq826616 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq826381
  have eq826750 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq32835 x
       grind)
    | (have r₁ := eq826616
       have r₂ := eq32835 x
       grind)
    | exact resolve eq826616 eq32835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32835 eq826616
  have eq826846 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq826750
       have i₂ := eq32960 x
       grind)
    | exact superpose eq32960 eq826750
    | exact resolve eq826750 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826750
  have eq826912 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33961 x X0
       have i₂ := eq826846
       grind)
    | exact superpose eq826846 eq33961
    | exact resolve eq33961 eq826846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33961
  have eq826923 : ∀ X0 : G, (M.op (τ (M.op (σ x) (σ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33996 x X0
       have i₂ := eq826846
       grind)
    | exact superpose eq826846 eq33996
    | exact resolve eq33996 eq826846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33996
  have eq826990 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq826846
       grind)
    | exact superpose eq826846 eq10
    | exact resolve eq10 eq826846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827439 : x = (M.op x x) := by
    first
    | (have i₁ := eq826990
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq826990
    | exact resolve eq826990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826990
  have eq827485 : ∀ X0 : G, (M.op (τ (σ (M.op x x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq826923 X0
       have i₂ := eq32960 x
       grind)
    | exact superpose eq32960 eq826923
    | exact resolve eq826923 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826923
  have eq827496 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq826912 X0
       have i₂ := eq32960 x
       grind)
    | exact superpose eq32960 eq826912
    | exact resolve eq826912 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32960 eq826912
  have eq827619 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq827485 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq827485
    | exact resolve eq827485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827485
  have eq827630 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq827496 X0
       have i₂ := eq826846
       grind)
    | exact superpose eq826846 eq827496
    | exact resolve eq827496 eq826846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826846 eq827496
  have eq827739 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq827619 X0
       have i₂ := eq827439
       grind)
    | exact superpose eq827439 eq827619
    | exact resolve eq827619 eq827439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827439 eq827619
  have eq834064 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq827630 (σ y)
       grind)
    | exact superpose eq827630 eq16
    | exact resolve eq16 eq827630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827630
  have eq834842 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq834064
       have i₂ := eq827739 y
       grind)
    | exact superpose eq827739 eq834064
    | exact resolve eq834064 eq827739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827739 eq834064
  have eq834843 : False := by grind
  exact eq834843

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq20 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq20 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq36 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | (have i₁ := eq34 X0 X1
       have i₂ := eq20 X0 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq20 eq34
    | exact resolve eq34 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq34
  have eq49 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq62 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq76 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq36 X1 (σ X0)
       grind)
    | exact superpose eq36 eq49
    | exact resolve eq49 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq86 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq76
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq147 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (τ (M.op (M.op X1 X1) X1))
       have i₂ := eq86 (σ X0) X1
       grind)
    | exact superpose eq86 eq49
    | exact resolve eq49 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq156 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op (M.op X1 X1) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq147
    | exact resolve eq147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq180 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq54
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq199 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op (M.op X1 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (τ (τ (M.op (M.op X1 X1) X1)))
       have i₂ := eq156 (σ X0) X1
       grind)
    | exact superpose eq156 eq49
    | exact resolve eq49 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq208 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (M.op (M.op X1 X1) X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq199
    | exact resolve eq199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq312 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ X2) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 (k X1 (τ X0)) X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq332 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (M.op (M.op X1 X1) X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (τ (τ (τ (M.op (M.op X1 X1) X1))))
       have i₂ := eq208 (σ X0) X1
       grind)
    | exact superpose eq208 eq49
    | exact resolve eq49 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq341 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (M.op (M.op X1 X1) X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq332
    | exact resolve eq332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq507 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (M.op (M.op X1 X1) X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (τ (τ (τ (τ (M.op (M.op X1 X1) X1)))))
       have i₂ := eq341 (σ X0) X1
       grind)
    | exact superpose eq341 eq49
    | exact resolve eq49 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq513 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (M.op (M.op X1 X1) X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq507 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq507
    | exact resolve eq507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq781 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (τ (M.op (M.op X1 X1) X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (τ (τ (τ (τ (τ (M.op (M.op X1 X1) X1))))))
       have i₂ := eq513 (σ X0) X1
       grind)
    | exact superpose eq513 eq49
    | exact resolve eq49 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq513
  have eq787 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (τ (M.op (M.op X1 X1) X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq781 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq781
    | exact resolve eq781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq6442 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) = (σ (k (τ (k X0 X1)) (τ (k X0 X1)))) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq180 (τ X1) X0
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq180
    | (have j0 := eq180 (τ X0) X1
       grind)
    | exact resolve eq180 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq180
  have eq6485 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) = (k (σ (τ (k X0 X1))) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6442 X0 X1
       have i₂ := eq19 (k X0 X1) (τ (k X0 X1))
       grind)
    | exact superpose eq19 eq6442
    | (have j0 := eq6442 X0 X1
       grind)
    | exact resolve eq6442 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6442
  have eq6501 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) = (k (k X0 X1) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6485 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6485
    | (have j0 := eq6485 X0 X1
       grind)
    | exact resolve eq6485 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6485
  have eq6516 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6501 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6501
    | (have j0 := eq6501 X0 X1
       grind)
    | exact resolve eq6501 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6501
  have eq6517 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6516 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6516
    | (have j0 := eq6516 X0 X1
       grind)
    | exact resolve eq6516 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6516
  have eq6518 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6517 X0 X1
       have j1 := eq12 (k X0 X1) (k X0 X1)
       grind)
    | (have r₁ := eq6517 X0 X1
       have r₂ := eq12 X0 (k X0 X1)
       grind)
    | exact resolve eq6517 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6517
  have eq6547 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6518 X0 (τ (τ (τ (τ (τ (τ (M.op (M.op x x) x)))))))
       have i₂ := eq787 X0 x
       grind)
    | exact superpose eq787 eq6518
    | exact resolve eq6518 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6518
  have eq6667 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6547 (σ X0)
       grind)
    | exact superpose eq6547 eq15
    | exact resolve eq15 eq6547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6687 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6667 X0
       have i₂ := eq6547 X0
       grind)
    | exact superpose eq6547 eq6667
    | exact resolve eq6667 eq6547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6547 eq6667
  have eq7631 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (σ (τ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k X0 (τ X1))
       have i₂ := eq312 X0 X1 (τ X2)
       grind)
    | exact superpose eq312 eq18
    | (have j1 := eq312 X0 X1 (τ X2)
       grind)
    | exact resolve eq18 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq312
  have eq7675 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (σ (τ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7631 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq7631
    | (have j0 := eq7631 X0 X1 X2
       grind)
    | exact resolve eq7631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7631
  have eq7694 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (σ (τ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7675 X0 X1 X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq7675
    | (have j0 := eq7675 X0 X1 X2
       grind)
    | exact resolve eq7675 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7675
  have eq7712 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (σ (τ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq7694 X0 X1 X2
       have j1 := eq12 X2 (k (σ X0) X1)
       grind)
    | (have r₁ := eq7694 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X0) X1)
       grind)
    | exact resolve eq7694 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7694
  have eq7730 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7712 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq7712
    | (have j0 := eq7712 X0 X1 X2
       grind)
    | exact resolve eq7712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7712
  have eq15684 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7730 X0 (τ (τ (τ (τ (τ (τ (M.op (M.op X1 X1) X1))))))) x
       have i₂ := eq787 (σ X0) X1
       grind)
    | exact superpose eq787 eq7730
    | exact resolve eq7730 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq7730
  have eq15729 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15684 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15684
    | exact resolve eq15684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15780 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq15684 X0 (σ X1)
       grind)
    | exact superpose eq15684 eq15
    | (have j1 := eq15684 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq15684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15684
  have eq15889 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq15729 (τ X0) X1
       grind)
    | exact superpose eq15729 eq19
    | (have j1 := eq15729 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq15729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15729
  have eq24561 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15889 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15889
    | exact resolve eq15889 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15889
  have eq24681 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24561 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq24561
    | (have j0 := eq24561 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq24561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24561
  have eq31850 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15780 x y
       grind)
    | exact superpose eq15780 eq16
    | (have j1 := eq15780 x y
       grind)
    | exact resolve eq16 eq15780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15780
  have eq31941 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31850
       have i₂ := eq24681 x y
       grind)
    | exact superpose eq24681 eq31850
    | (have j1 := eq24681 (σ x) (σ y)
       grind)
    | (have r₁ := eq31850
       have r₂ := eq24681 x y
       grind)
    | (have r₁ := eq31850
       have r₂ := eq24681 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq31850
       have r₂ := eq24681 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq31850 eq24681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24681 eq31850
  have eq31944 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq31941
  have eq32366 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31944
       grind)
    | exact superpose eq31944 eq16
    | exact resolve eq16 eq31944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31944
  have eq32367 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq32366
       have r₂ := eq6687 x
       grind)
    | exact resolve eq32366 eq6687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32366
  have eq32368 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32367
       grind)
    | exact superpose eq32367 eq16
    | exact resolve eq16 eq32367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32369 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq32367
       grind)
    | exact superpose eq32367 eq10
    | exact resolve eq10 eq32367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32367
  have eq32464 : x = y := by
    first
    | (have i₁ := eq32369
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq32369
    | exact resolve eq32369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32369
  have eq32465 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq32368
       have i₂ := eq6687 x
       grind)
    | exact superpose eq6687 eq32368
    | exact resolve eq32368 eq6687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6687 eq32368
  have eq32471 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq32465
       have i₂ := eq32464
       grind)
    | exact superpose eq32464 eq32465
    | exact resolve eq32465 eq32464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32464 eq32465
  have eq32472 : False := by grind
  exact eq32472

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pxx_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq53 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq75 eq77
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq420 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq53
    | exact resolve eq53 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq420 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq53 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq53 eq420
    | exact resolve eq420 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq960 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq900 X0 X1
       have i₂ := eq82 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq82 eq900
    | exact resolve eq900 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq900
  have eq972 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq960 X0 X1
       have i₂ := eq53 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq960 X0 X1
       have i₂ := eq53 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq53 eq960
    | exact resolve eq960 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq17739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq17740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq17739
    | exact resolve eq17739 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17739
  have eq17751 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17740
       have r₂ := eq28
       grind)
    | exact resolve eq17740 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17740
  have eq17755 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq17751 eq80
    | exact resolve eq80 eq17751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17751
  have eq17811 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq17755
    | exact resolve eq17755 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17755
  have eq17812 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17811
  have eq17827 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq17812
       grind)
    | exact superpose eq17812 eq53
    | exact resolve eq53 eq17812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17812
  have eq18954 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq17827 x
       grind)
    | exact superpose eq17827 eq53
    | exact resolve eq53 eq17827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq18959 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq972 x X0
       have i₂ := eq17827 x
       grind)
    | exact superpose eq17827 eq972
    | exact resolve eq972 eq17827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq17827
  have eq19065 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18959 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18959
    | (have j0 := eq18959 X0
       grind)
    | exact resolve eq18959 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18959
  have eq19067 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18954 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18954
    | (have j0 := eq18954 y
       grind)
    | exact resolve eq18954 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18954
  have eq19191 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19067 eq30
    | exact resolve eq30 eq19067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19067
  have eq19312 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq19191
    | exact resolve eq19191 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19191
  have eq19313 : y = (M.op x y) ∨ x = y := by grind
  clear eq19312
  have eq19460 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq19313 eq21
    | exact resolve eq21 eq19313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19313
  have eq19572 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19460
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19460
    | exact resolve eq19460 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19460
  have eq19588 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq19572 eq27
    | exact resolve eq27 eq19572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19572
  have eq21083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19065 eq19588
    | exact resolve eq19588 eq19065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19065 eq19588
  have eq21160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq21083
  have eq21200 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq21160
       have r₂ := eq28
       grind)
    | exact resolve eq21160 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21160
  have eq21209 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq21200 eq30
    | exact resolve eq30 eq21200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq21200
  have eq21355 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq21209
    | exact resolve eq21209 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21209
  have eq21356 : x = y := by grind
  clear eq21355
  have eq21372 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq21356
       grind)
    | exact superpose eq21356 eq19
    | exact resolve eq19 eq21356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21373 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq21356
       grind)
    | exact superpose eq21356 eq25
    | exact resolve eq25 eq21356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq21356
  have eq21485 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq21373
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21373
    | exact resolve eq21373 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21373
  have eq21501 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21485 eq27
    | exact resolve eq27 eq21485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21485
  have eq21750 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq21501 eq80
    | exact resolve eq80 eq21501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq21501
  have eq21801 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq21750
       have i₂ := eq21372
       grind)
    | exact superpose eq21372 eq21750
    | exact resolve eq21750 eq21372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21372 eq21750
  have eq21808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21801 eq15
    | exact resolve eq15 eq21801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21801
  have eq21857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq21808
    | exact resolve eq21808 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq21808
  have eq21866 : False := by grind
  exact eq21866

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation2994 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2994 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq85 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
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
  have eq86 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq14937
    | exact resolve eq14937 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14937
  have eq14949 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq14938
       have r₂ := eq28
       grind)
    | exact resolve eq14938 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14938
  have eq14953 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq14949
    | exact resolve eq14949 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14949
  have eq14958 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq14953 eq86
    | (have r₁ := eq86
       have r₂ := eq14953
       grind)
    | exact resolve eq86 eq14953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq14953
  have eq14985 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq14958
  have eq14986 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq14985
  have eq14994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq14986 eq77
    | exact resolve eq77 eq14986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq14986
  have eq15006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14994
  have eq15009 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15006
       have r₂ := eq28
       grind)
    | exact resolve eq15006 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15006
  have eq15136 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq15009
       grind)
    | exact superpose eq15009 eq52
    | exact resolve eq52 eq15009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq15138 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq15009
       grind)
    | exact superpose eq15009 eq85
    | (have r₁ := eq85
       have r₂ := eq15009
       grind)
    | exact resolve eq85 eq15009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq15009
  have eq15164 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq15138
  have eq15165 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15164
  have eq15176 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq15136
    | exact resolve eq15136 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15136
  have eq15184 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15165
       grind)
    | exact superpose eq15165 eq49
    | exact resolve eq49 eq15165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq15165
  have eq15206 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq15184
    | exact resolve eq15184 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15184
  have eq15415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15206 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq15206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15206
  have eq15416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15415
  have eq15420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq15416
    | exact resolve eq15416 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15416
  have eq15431 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq15420
       have r₂ := eq28
       grind)
    | exact resolve eq15420 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15420
  have eq15435 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq15431
    | exact resolve eq15431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15431
  have eq15448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15435 eq15176
    | exact resolve eq15176 eq15435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15176 eq15435
  have eq15469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15448
  have eq15475 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq15469
       have r₂ := eq28
       grind)
    | exact resolve eq15469 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15469
  have eq15603 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq15475 eq30
    | exact resolve eq30 eq15475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15475
  have eq15717 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq15603
    | exact resolve eq15603 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15603
  have eq15718 : x = y := by grind
  clear eq15717
  have eq15737 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15718
       grind)
    | exact superpose eq15718 eq19
    | exact resolve eq19 eq15718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15738 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15718
       grind)
    | exact superpose eq15718 eq25
    | exact resolve eq25 eq15718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15718
  have eq15847 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15738
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15738
    | exact resolve eq15738 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15738
  have eq15862 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15847 eq27
    | exact resolve eq27 eq15847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15847
  have eq16068 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15862 eq68
    | exact resolve eq68 eq15862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq15862
  have eq16106 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16068
       have i₂ := eq15737
       grind)
    | exact superpose eq15737 eq16068
    | exact resolve eq16068 eq15737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15737 eq16068
  have eq16115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16106 eq15
    | exact resolve eq15 eq16106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16106
  have eq16163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16115
    | exact resolve eq16115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16115
  have eq16172 : False := by grind
  exact eq16172

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pyy_pxy_Equation2994 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2994 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq55 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x (M.op x x)
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq408 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq55
    | exact resolve eq55 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq408 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq55 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq55 eq408
    | exact resolve eq408 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq901 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq45 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq45 eq841
    | exact resolve eq841 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq841
  have eq912 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq901 X0 X1
       have i₂ := eq55 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq901 X0 X1
       have i₂ := eq55 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq55 eq901
    | exact resolve eq901 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq18134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq76 eq11
    | (have j0 := eq11 (σ x) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq18135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq18134
    | exact resolve eq18134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18134
  have eq18146 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq18135
       have r₂ := eq28
       grind)
    | exact resolve eq18135 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18135
  have eq18956 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq18146 eq68
    | exact resolve eq68 eq18146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18146
  have eq19018 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq18956
    | exact resolve eq18956 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18956
  have eq19019 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19018
  have eq19035 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq19019
       grind)
    | exact superpose eq19019 eq55
    | exact resolve eq55 eq19019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19019
  have eq20084 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq19035 x
       grind)
    | exact superpose eq19035 eq55
    | exact resolve eq55 eq19035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq20090 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq912 x X0
       have i₂ := eq19035 x
       grind)
    | exact superpose eq19035 eq912
    | exact resolve eq912 eq19035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912 eq19035
  have eq20192 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20090 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20090
    | (have j0 := eq20090 X0
       grind)
    | exact resolve eq20090 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20090
  have eq20198 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq20084 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20084
    | (have j0 := eq20084 y
       grind)
    | exact resolve eq20084 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20084
  have eq20322 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20198 eq30
    | exact resolve eq30 eq20198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20198
  have eq20433 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq20322
    | exact resolve eq20322 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20322
  have eq20434 : y = (M.op x y) ∨ x = y := by grind
  clear eq20433
  have eq20927 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20434 eq21
    | exact resolve eq21 eq20434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20434
  have eq21039 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20927
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20927
    | exact resolve eq20927 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20927
  have eq21055 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq21039 eq27
    | exact resolve eq27 eq21039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21039
  have eq24260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20192 eq21055
    | exact resolve eq21055 eq20192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20192 eq21055
  have eq24367 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq24260
  have eq24408 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq24367
       have r₂ := eq28
       grind)
    | exact resolve eq24367 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24367
  have eq24422 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq24408 eq30
    | exact resolve eq30 eq24408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq24408
  have eq24554 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq24422
    | exact resolve eq24422 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq24422
  have eq24555 : x = y := by grind
  clear eq24554
  have eq25233 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq24555
       grind)
    | exact superpose eq24555 eq19
    | exact resolve eq19 eq24555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq25234 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq24555
       grind)
    | exact superpose eq24555 eq25
    | exact resolve eq25 eq24555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq24555
  have eq25346 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25234
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25234
    | exact resolve eq25234 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq25234
  have eq25362 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25346 eq27
    | exact resolve eq27 eq25346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25346
  have eq25613 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq25362 eq68
    | exact resolve eq68 eq25362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq25362
  have eq25678 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq25613
       have i₂ := eq25233
       grind)
    | exact superpose eq25233 eq25613
    | exact resolve eq25613 eq25233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25233 eq25613
  have eq25687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25678 eq15
    | exact resolve eq15 eq25678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25678
  have eq25736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq25687
    | exact resolve eq25687 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25687
  have eq25745 : False := by grind
  exact eq25745

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_x_pyx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  clear eq43
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq49
    | exact resolve eq49 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq70
    | exact resolve eq70 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq70
  have eq77 : y ≠ (M.op x y) ∨ (M.op x x) = (M.op y x) ∨ y = (k y x) := by
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
  have eq87 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
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
  have eq93 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22 eq36
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq87 y x
       grind)
    | exact superpose eq87 eq93
    | (have j1 := eq87 y x
       grind)
    | exact resolve eq93 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq125
    | exact resolve eq125 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq128 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq127
    | exact resolve eq127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128 eq87
    | (have j0 := eq87 (σ y) (σ x)
       grind)
    | exact resolve eq87 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq197
    | exact resolve eq197 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq201 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq198
       have r₂ := eq27
       grind)
    | exact resolve eq198 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq203 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq201
    | exact resolve eq201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq264 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq203 eq51
    | exact resolve eq51 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq203
  have eq275 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (σ y) (σ y)) (σ x))) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq264 eq14
    | exact resolve eq14 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ y) (σ y)) (σ x))) X0) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq264 eq14
    | exact resolve eq14 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq275 eq276
    | exact resolve eq276 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq276
  have eq342 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq331 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq357 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq264 X0
       have i₂ := eq342 sF3 sF2
       grind)
    | exact superpose eq342 eq264
    | exact resolve eq264 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq368 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq357 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq379 : (τ (σ x)) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq368 eq71
    | exact resolve eq71 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq368
  have eq392 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq379
    | exact resolve eq379 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq379
  have eq429 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq342 x X0
       have i₂ := eq392
       grind)
    | exact superpose eq392 eq342
    | exact resolve eq342 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq392
  have eq433 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq438 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq433 y
       grind)
    | exact superpose eq433 eq18
    | (have j1 := eq433 y
       grind)
    | exact resolve eq18 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq452 : y = (M.op x y) := by grind
  clear eq438
  have eq455 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq452 eq20
    | exact resolve eq20 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq467 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq455
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq455
    | exact resolve eq455 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq525 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq467 eq26
    | exact resolve eq26 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq631 : (M.op x x) = (M.op y x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq77
       have r₂ := eq452
       grind)
    | exact resolve eq77 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq657 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq631
       grind)
    | exact superpose eq631 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq631
       grind)
    | exact resolve eq13 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq659 : (M.op x y) = (k y x) ∨ y = (k y x) := by grind
  clear eq657
  have eq660 : (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq659
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq659
    | exact resolve eq659 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq659
  have eq662 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq452 eq660
    | exact resolve eq660 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq660
  have eq663 : y = (k y x) := by grind
  clear eq662
  have eq668 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq663
       grind)
    | exact superpose eq663 eq93
    | exact resolve eq93 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq663
  have eq675 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq467 eq668
    | exact resolve eq668 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq677 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq675
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq675
    | exact resolve eq675 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq675
  have eq678 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq467 eq677
    | exact resolve eq677 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq677
  have eq681 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq678 eq87
    | (have j0 := eq87 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq87 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq678
  have eq682 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq681
  have eq684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq525 eq682
    | exact resolve eq682 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq682
  have eq687 : False := by grind
  exact eq687

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_y_pyx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  clear eq43
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq74
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq74
    | exact resolve eq74 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq72
    | exact resolve eq72 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq72
  have eq89 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
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
  have eq95 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq89 y x
       grind)
    | exact superpose eq89 eq95
    | (have j1 := eq89 x x
       grind)
    | exact resolve eq95 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq127
    | exact resolve eq127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq659 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op X0 X0) x x X3
       have i₂ := eq52 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq688 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq659 (σ X0) X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq659
    | exact resolve eq659 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq129 eq89
    | (have j0 := eq89 x (σ x)
       grind)
    | exact resolve eq89 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq129
  have eq1022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq1021
    | exact resolve eq1021 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1025 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1022
       have r₂ := eq27
       grind)
    | exact resolve eq1022 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1028 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1025 eq75
    | exact resolve eq75 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1025
  have eq1045 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq1028
    | exact resolve eq1028 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1028
  have eq1046 : x = (M.op x x) := by grind
  clear eq1045
  have eq1055 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq688 x X0
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq688
    | exact resolve eq688 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq1056 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq659 x X0
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq659
    | exact resolve eq659 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq1046
  have eq1062 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1055 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1055
    | (have j0 := eq1055 X0
       grind)
    | exact resolve eq1055 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1055
  have eq1119 : y = (M.op x y) := by
    first
    | (have i₁ := eq1056 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1056
    | (have j0 := eq1056 y
       grind)
    | exact resolve eq1056 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1056
  have eq1156 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1119 eq20
    | exact resolve eq20 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1119
  have eq1175 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1156
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1156
    | exact resolve eq1156 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1156
  have eq1202 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1062 eq26
    | (have j1 := eq1062 (σ y)
       grind)
    | exact resolve eq26 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1062
  have eq1234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1175 eq1202
    | exact resolve eq1202 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175 eq1202
  have eq1239 : False := by grind
  exact eq1239

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X0) (σ X1)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq35 (σ X0) X1 X2
       grind)
    | exact superpose eq35 eq31
    | exact resolve eq31 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq35 (τ X0) X1 X2
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35
  have eq84 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq85 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq105 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 (M.op (M.op X1 X1) X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq24 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq24 eq84
    | exact resolve eq84 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq146 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op X0 X0) x x X3
       have i₂ := eq24 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq169 : ∀ X0 X1 X2 X3 X4 : G, (k X3 (σ (M.op X4 (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X4)))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq105 X4 (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3
       have i₂ := eq24 X0 X1 X2 (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2))
       grind)
    | exact superpose eq24 eq105
    | exact resolve eq105 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq182 : ∀ X3 X4 : G, (k X3 (σ (M.op X4 X4))) = X3 := by
    intro X3 X4
    first
    | (have i₁ := eq169 x x x X3 X4
       have i₂ := eq24 x x x X4
       grind)
    | exact superpose eq24 eq169
    | exact resolve eq169 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq169
  have eq192 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq70 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq214 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ (M.op X1 X1))
       have i₂ := eq182 (σ X0) X1
       grind)
    | exact superpose eq182 eq31
    | exact resolve eq31 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq182
  have eq219 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq214
    | exact resolve eq214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq220 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq219
    | exact resolve eq219 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq247 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op (M.op X0 X0) (M.op X2 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85 X1 X0 (M.op X2 X2)
       have i₂ := eq146 X2 X0
       grind)
    | exact superpose eq146 eq85
    | exact resolve eq85 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq265 : ∀ X1 X2 : G, (k X1 (τ (M.op X2 X2))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq247 x X1 X2
       have i₂ := eq146 x (M.op X2 X2)
       grind)
    | (have i₁ := eq247 x X1 X2
       have i₂ := eq146 x (M.op (M.op x x) (M.op X2 X2))
       grind)
    | exact superpose eq146 eq247
    | exact resolve eq247 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq563 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq192
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq192
    | (have j1 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq192 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq192
  have eq564 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq563
  have eq1526 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq203 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq203
    | (have j0 := eq203 (τ X0)
       grind)
    | exact resolve eq203 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1554 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1526 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1526
    | (have j0 := eq1526 X0
       grind)
    | exact resolve eq1526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1569 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1554 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1554
    | (have j0 := eq1554 X0
       grind)
    | exact resolve eq1554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq1685 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq146 y X0
       have i₂ := eq564
       grind)
    | exact superpose eq564 eq146
    | exact resolve eq146 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq2372 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 (σ y)
       have i₂ := eq1685 X1
       grind)
    | exact superpose eq1685 eq265
    | (have j1 := eq1685 X1
       grind)
    | exact resolve eq265 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq1685
  have eq2401 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2372 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2372
    | (have j0 := eq2372 X0 X1
       grind)
    | exact resolve eq2372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372
  have eq2405 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1569 x
       have i₂ := eq2401 x X0
       grind)
    | exact superpose eq2401 eq1569
    | (have j0 := eq1569 x
       have j1 := eq2401 X0 x
       grind)
    | (have r₁ := eq1569 x
       have r₂ := eq2401 x x
       grind)
    | exact resolve eq1569 eq2401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569 eq2401
  have eq2419 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2405 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2463 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq2419 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419
  have eq2464 : x = (M.op x x) := by grind
  clear eq2463
  have eq2697 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq146 x X0
       have i₂ := eq2464
       grind)
    | exact superpose eq2464 eq146
    | exact resolve eq146 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2700 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq220 X0 x
       have i₂ := eq2464
       grind)
    | exact superpose eq2464 eq220
    | exact resolve eq220 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq2464
  have eq2840 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq203 x
       have i₂ := eq2700 x
       grind)
    | exact superpose eq2700 eq203
    | (have j0 := eq203 x
       grind)
    | exact resolve eq203 eq2700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq2700
  have eq2852 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2840
  have eq6067 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq146 (σ x) X0
       have i₂ := eq2852
       grind)
    | exact superpose eq2852 eq146
    | exact resolve eq146 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq2852
  have eq6130 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6067 (σ y)
       grind)
    | exact superpose eq6067 eq16
    | exact resolve eq16 eq6067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6067
  have eq6265 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6130
       have i₂ := eq2697 y
       grind)
    | exact superpose eq2697 eq6130
    | exact resolve eq6130 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697 eq6130
  have eq6266 : False := by grind
  exact eq6266
