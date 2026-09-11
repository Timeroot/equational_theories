import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq58 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq58
    | exact resolve eq58 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X2 X3) (M.op X1 X0))) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq123 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq133 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq145 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq66 X1 X1
       grind)
    | exact superpose eq66 eq85
    | exact resolve eq85 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq85
  have eq289 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 (M.op X0 X0) X2 X1
       have i₂ := eq146 X0 X0
       grind)
    | exact superpose eq146 eq63
    | exact resolve eq63 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq146 X1 X3
       have i₂ := eq289 X1 X2 X0
       grind)
    | exact superpose eq289 eq146
    | exact resolve eq146 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq335 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X1
       have i₂ := eq289 X1 X2 X0
       grind)
    | exact superpose eq289 eq60
    | exact resolve eq60 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq342 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 (M.op X0 X1) X1 X3 X2
       have i₂ := eq289 X1 X1 X0
       grind)
    | exact superpose eq289 eq63
    | exact resolve eq63 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq352 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X1 x x
       have i₂ := eq63 X1 X1 x x
       grind)
    | exact superpose eq63 eq342
    | exact resolve eq342 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq342
  have eq378 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq422 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq426 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq378 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq480 : ∀ X0 X2 X3 : G, (M.op X3 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq335 (M.op x (M.op X2 X2)) X3 (M.op X2 (M.op X0 X0))
       have i₂ := eq145 x X2 X0
       grind)
    | exact superpose eq145 eq335
    | exact resolve eq335 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq492 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) X1) = (M.op (M.op (M.op X2 (M.op X0 X1)) X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq335 X0 (M.op (M.op X2 (M.op X0 X1)) X1) X1
       have i₂ := eq335 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq335 eq335
    | exact resolve eq335 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq492 X0 X1 X2
       have i₂ := eq352 (M.op X2 (M.op X0 X1)) X1
       grind)
    | exact superpose eq352 eq492
    | exact resolve eq492 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq610 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq335 X0 (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) (M.op X1 X2)
       have i₂ := eq334 X3 X2 (M.op X0 (M.op X1 X2)) X1
       grind)
    | exact superpose eq334 eq335
    | exact resolve eq335 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq335
  have eq626 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq610 X0 X1 X2 X3
       have i₂ := eq352 (M.op X3 (M.op X0 (M.op X1 X2))) X2
       grind)
    | exact superpose eq352 eq610
    | exact resolve eq610 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq610
  have eq836 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq117 X1 X0 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq117
    | (have j0 := eq117 X1 X0 x x
       grind)
    | exact resolve eq117 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1666 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq426 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq1687 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = (k X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1666 X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq504 X1 X2 X0
       grind)
    | exact superpose eq504 eq1666
    | (have j0 := eq1666 X2 X2
       grind)
    | (have r₁ := eq1666 X1 (M.op X2 (M.op X0 X1))
       have r₂ := eq504 X0 X1 X2
       grind)
    | exact resolve eq1666 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq1666
  have eq1691 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1687 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq2334 : ∀ X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X2)) = (k (M.op X1 X2) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq1691 X2 (M.op x (M.op X1 X1)) (M.op X1 X2)
       have i₂ := eq480 X1 x X2
       grind)
    | exact superpose eq480 eq1691
    | exact resolve eq1691 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq1691
  have eq2371 : ∀ X1 X2 : G, (M.op X2 (M.op X1 X2)) = (k (M.op X1 X2) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq2334 X1 X2
       have i₂ := eq31 X1 X2
       grind)
    | exact superpose eq31 eq2334
    | exact resolve eq2334 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2334
  have eq4558 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq626 X1 X0 X1 X1
       have i₂ := eq836 X0 X1
       grind)
    | exact superpose eq836 eq626
    | (have j1 := eq836 X0 X1
       grind)
    | exact resolve eq626 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq836
  have eq4700 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4558 X0 X1
       have j1 := eq422 X1 X0
       grind)
    | (have r₁ := eq4558 X1 X0
       have r₂ := eq422 X0 X1
       grind)
    | (have r₁ := eq4558 X0 X0
       have r₂ := eq422 X0 X0
       grind)
    | (have r₁ := eq4558 X0 (M.op X1 X0)
       have r₂ := eq422 X0 X1
       grind)
    | exact resolve eq4558 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq4558
  have eq4854 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2371 X0 X0
       have i₂ := eq4700 X0 X1
       grind)
    | (have i₁ := eq2371 X1 x
       have i₂ := eq4700 X0 (M.op X1 x)
       grind)
    | exact superpose eq4700 eq2371
    | (have j1 := eq4700 X0 X1
       grind)
    | exact resolve eq2371 eq4700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371 eq4700
  have eq4862 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4854 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4854
  have eq4911 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4862 (σ X1) (σ X0)
       grind)
    | exact superpose eq4862 eq15
    | exact resolve eq15 eq4862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4923 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4911 X0 X1
       have i₂ := eq4862 X1 X0
       grind)
    | exact superpose eq4862 eq4911
    | exact resolve eq4911 eq4862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4862 eq4911
  have eq5043 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4923 y x
       grind)
    | exact superpose eq4923 eq16
    | (have r₁ := eq16
       have r₂ := eq4923 y x
       grind)
    | exact resolve eq16 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4923
  have eq5070 : False := by grind
  exact eq5070

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq116 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X2 X0) X2 x X1
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq518 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq166
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq166
    | exact resolve eq166 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq554 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq518
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq518
    | (have j1 := eq56 y x
       grind)
    | exact resolve eq518 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq518
  have eq555 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq554
  have eq736 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq116 (σ X0) X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq116
    | exact resolve eq116 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23561 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ y) (σ (M.op y y)))) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq116 (σ x) X0 (σ y)
       have i₂ := eq555
       grind)
    | exact superpose eq555 eq116
    | exact resolve eq116 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq23636 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq23561 x
       have i₂ := eq736 y x
       grind)
    | exact superpose eq736 eq23561
    | exact resolve eq23561 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq23561
  have eq23682 : y = (τ (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23636
       grind)
    | exact superpose eq23636 eq10
    | exact resolve eq10 eq23636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23636
  have eq23742 : x = y ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq23682
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23682
    | exact resolve eq23682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23682
  have eq24252 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23742
       grind)
    | exact superpose eq23742 eq16
    | exact resolve eq16 eq23742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23742
  have eq24253 : (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq24252
       have r₂ := eq95 x
       grind)
    | exact resolve eq24252 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24252
  have eq24319 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq116 y X0 y
       have i₂ := eq24253
       grind)
    | exact superpose eq24253 eq116
    | exact resolve eq116 eq24253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24253
  have eq24419 : x = y := by
    first
    | (have i₁ := eq24319 x
       have i₂ := eq116 x x y
       grind)
    | exact superpose eq116 eq24319
    | exact resolve eq24319 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq24319
  have eq24487 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24419
       grind)
    | exact superpose eq24419 eq16
    | exact resolve eq16 eq24419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24419
  have eq24489 : False := by grind
  exact eq24489

/-- `Equation968`: `x = y ◇ ((z ◇ y) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyy_x_pxy_pxx_pxy_Equation968 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law968 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law968.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X2 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op x X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X0 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X1 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X2) (M.op X3 X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq44
    | exact resolve eq44 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq45
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq45 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq104
    | exact resolve eq104 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq108
    | exact resolve eq108 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq125 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq138 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq156 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq153
       have i₂ := eq66 sF1
       grind)
    | exact superpose eq66 eq153
    | exact resolve eq153 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq158 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq156
       have i₂ := eq66 sF0
       grind)
    | exact superpose eq66 eq156
    | exact resolve eq156 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq156
  have eq217 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq77 (σ X0) sF3
       grind)
    | exact superpose eq77 eq41
    | (have j1 := eq77 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op (M.op X1 x) (M.op X1 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X1 x) (M.op X1 X0))
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x X0)) (M.op X0 (M.op y X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (M.op X1 (σ x)) (M.op X1 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op x sF2) (M.op x X0))
       have i₂ := eq14 X0 sF2 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X1 x) (M.op X1 X0)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X1 x) (M.op X1 X0))
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (M.op (M.op x X1) (M.op x y)) = (M.op X0 (M.op (M.op X1 X0) y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : (M.op (M.op x x) (M.op x y)) = (M.op y (M.op (M.op x y) y)) := by
    first
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X1 (σ x)) (M.op X1 X0)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op (M.op x sF2) (M.op x X0))
       have i₂ := eq14 X0 sF2 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X1 X0) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : (M.op (M.op (σ x) x) (M.op (σ x) (σ y))) = (M.op y (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (σ y)) (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq531 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 (M.op x X1)) (M.op X0 X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) (M.op X1 (M.op X1 X2)) (M.op X1 X2)
       have i₂ := eq53 (M.op X1 X2) X1 X2 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X1 (M.op X4 (M.op X3 X0)))) = (M.op (M.op X2 X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op X4 (M.op X3 X0)) (M.op X2 X4) (M.op X2 X3) X1
       have i₂ := eq53 X4 X2 X3 X0
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op x (M.op X1 X2)) (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X2 X0) x X2 X1
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq56 X2 X0 X1 x
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq97 eq77
    | (have j0 := eq77 (σ x) (σ y)
       grind)
    | exact resolve eq77 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq97
  have eq974 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq973
    | exact resolve eq973 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq977 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq974
       have r₂ := eq28
       grind)
    | exact resolve eq974 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq979 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq977 eq138
    | exact resolve eq138 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq977
  have eq995 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq979
    | exact resolve eq979 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq979
  have eq996 : x = (M.op y y) := by grind
  clear eq995
  have eq1007 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X0 X0) X1) (M.op X0 (M.op X0 X0)))) = X0 ∨ (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq14
    | (have j1 := eq125 X0
       grind)
    | exact resolve eq14 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq1026 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq110
    | exact resolve eq110 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1031 : ∀ X0 : G, (M.op y (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq14
    | exact resolve eq14 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1032 : ∀ X0 : G, y = (M.op X0 (M.op (M.op y X0) x)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 y
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq14
    | exact resolve eq14 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1026
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1026
    | exact resolve eq1026 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1050 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1044 eq14
    | exact resolve eq14 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1051 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ y) X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq1044 eq14
    | exact resolve eq14 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1067 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq1031 y
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq1031
    | exact resolve eq1031 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq54 eq1031
    | exact resolve eq1031 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1080 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1069
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1069
    | exact resolve eq1069 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1124 : (M.op x x) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1031 (M.op x x)
       have i₂ := eq1067
       grind)
    | exact superpose eq1067 eq1031
    | exact resolve eq1031 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1134 : (M.op x x) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1124
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1124
    | exact resolve eq1124 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1136 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) := by
    first
    | exact superpose eq1080 eq158
    | exact resolve eq158 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1204 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1134 eq1136
    | exact resolve eq1136 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1205 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1204
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq1204
    | exact resolve eq1204 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1204
  have eq1283 : y = (M.op (M.op (M.op y y) x) (M.op y x)) := by
    first
    | (have i₁ := eq1032 (M.op (M.op y y) x)
       have i₂ := eq1032 y
       grind)
    | exact superpose eq1032 eq1032
    | exact resolve eq1032 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1285 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1032 x
       have i₂ := eq56 x x y X0
       grind)
    | exact superpose eq56 eq1032
    | exact resolve eq1032 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1306 : y = (M.op (M.op x x) (M.op y x)) := by
    first
    | (have i₁ := eq1283
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq1283
    | exact resolve eq1283 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1316 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1044 eq1050
    | exact resolve eq1050 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1333 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1205 eq1316
    | exact resolve eq1316 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1356 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1333 eq1050
    | exact resolve eq1050 eq1333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050 eq1333
  have eq1366 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq1356
    | exact resolve eq1356 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq1412 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1051 x
       have i₂ := eq56 sF2 x sF3 x
       grind)
    | exact superpose eq56 eq1051
    | exact resolve eq1051 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1051
  have eq1462 : y = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq1285 y
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq1285
    | exact resolve eq1285 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1502 : (M.op y x) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq51 (M.op y x)
       have i₂ := eq1462
       grind)
    | exact superpose eq1462 eq51
    | exact resolve eq51 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1537 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1366 eq266
    | exact resolve eq266 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq1538 : (σ y) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1205 eq1537
    | exact resolve eq1537 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq1537
  have eq1541 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | exact superpose eq1044 eq1412
    | exact resolve eq1412 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1738 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op X0 y) (M.op X0 X1)) (M.op X1 (M.op y x))) := by
    intro X0 X1
    first
    | exact superpose eq1502 eq53
    | exact resolve eq53 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1742 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1738 x x
       have i₂ := eq53 x x y x
       grind)
    | exact superpose eq53 eq1738
    | exact resolve eq1738 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq1770 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x x) (M.op y (M.op (M.op x y) y))) X0) := by
    intro X0
    first
    | exact superpose eq261 eq539
    | exact resolve eq539 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq1780 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq244 eq539
    | exact resolve eq539 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1886 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq1080 eq1780
    | exact resolve eq1780 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq1780
  have eq1888 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x x) (M.op y x)) X0) := by
    intro X0
    first
    | exact superpose eq1502 eq1770
    | exact resolve eq1770 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq1900 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | exact superpose eq1134 eq1886
    | exact resolve eq1886 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq1901 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq1888 X0
       have i₂ := eq1306
       grind)
    | exact superpose eq1306 eq1888
    | exact resolve eq1888 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306 eq1888
  have eq1904 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq1900 X0
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq1900
    | exact resolve eq1900 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq2069 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq244 eq680
    | exact resolve eq680 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq2076 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1541 eq680
    | exact resolve eq680 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq2082 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq248 eq680
    | exact resolve eq680 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq2103 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq1366 eq2082
    | exact resolve eq2082 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366 eq2082
  have eq2106 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq2076
    | exact resolve eq2076 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2076
  have eq2109 : (M.op x y) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq1134 eq2069
    | exact resolve eq2069 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq2069
  have eq2321 : ∀ X0 : G, (M.op x (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq685 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq685
    | (have j0 := eq685 y x X0
       grind)
    | exact resolve eq685 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2371 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2103 eq685
    | exact resolve eq685 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq2460 : ∀ X0 : G, (M.op x (M.op y (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1901 eq2321
    | exact resolve eq2321 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq2485 : y = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq685 x x y
       have i₂ := eq2109
       grind)
    | exact superpose eq2109 eq685
    | exact resolve eq685 eq2109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq2513 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq2371 eq539
    | exact resolve eq539 eq2371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq2527 : (M.op x (M.op x y)) = (M.op y (M.op (M.op x y) y)) := by
    first
    | exact superpose eq2485 eq51
    | exact resolve eq51 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2485
  have eq2544 : (M.op y x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq1502 eq2527
    | exact resolve eq2527 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502 eq2527
  have eq2735 : ∀ X0 X1 : G, (M.op (M.op X1 x) (M.op X1 X0)) = (M.op y (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq1901 eq245
    | exact resolve eq245 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq2844 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2735 (M.op x X0) x
       have i₂ := eq680 X0 x x
       grind)
    | exact superpose eq680 eq2735
    | exact resolve eq2735 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2849 : ∀ X0 X2 : G, (M.op (M.op y (M.op y X0)) (M.op X0 (M.op x X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq53 X0 x x X2
       have i₂ := eq2735 X0 x
       grind)
    | exact superpose eq2735 eq53
    | exact resolve eq53 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2890 : ∀ X0 X2 : G, (M.op X0 (M.op X0 (M.op x X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq2849 X0 X2
       have i₂ := eq539 (M.op X0 (M.op x X2)) y X0
       grind)
    | exact superpose eq539 eq2849
    | exact resolve eq2849 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2849
  have eq3172 : ∀ X0 X1 : G, (M.op (M.op y (M.op x X0)) (M.op X0 (M.op y X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1901 eq247
    | exact resolve eq247 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq3426 : ∀ X0 X1 : G, (M.op (M.op X1 (σ x)) (M.op X1 X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq2513 eq249
    | exact resolve eq249 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq3528 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq3426 eq14
    | exact resolve eq14 eq3426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4206 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq257 X0 x
       have i₂ := eq2735 X0 x
       grind)
    | exact superpose eq2735 eq257
    | exact resolve eq257 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq4207 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4206 x
       have i₂ := eq539 (M.op x sF0) y x
       grind)
    | exact superpose eq539 eq4206
    | exact resolve eq4206 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4206
  have eq4221 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | exact superpose eq4207 eq680
    | exact resolve eq680 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4460 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq259 X0 X0
       have i₂ := eq4221 X0
       grind)
    | exact superpose eq4221 eq259
    | exact resolve eq259 eq4221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq4221
  have eq5380 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3426 eq264
    | exact resolve eq264 eq3426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq3426
  have eq5381 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq5380 x
       have i₂ := eq539 (M.op x sF4) sF3 x
       grind)
    | exact superpose eq539 eq5380
    | exact resolve eq5380 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5380
  have eq5394 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq5381 eq680
    | exact resolve eq680 eq5381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5433 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5381 eq52
    | exact resolve eq52 eq5381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq5381
  have eq5442 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2106 eq5433
    | exact resolve eq5433 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106 eq5433
  have eq5478 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5394 (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq5394
    | exact resolve eq5394 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq5394
  have eq5630 : (M.op (M.op (σ x) (M.op (σ x) x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op y (M.op (M.op x y) (σ y))) (σ y))) := by
    first
    | exact superpose eq270 eq267
    | exact resolve eq267 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq270
  have eq5812 : (M.op (M.op (σ x) (M.op (σ x) x)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op y (M.op (M.op x y) (σ y))) (σ y))) := by
    first
    | exact superpose eq2513 eq5630
    | exact resolve eq5630 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513 eq5630
  have eq5897 : (M.op (M.op (σ x) (M.op (σ x) x)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op y (M.op y (σ y))) (σ y))) := by
    first
    | exact superpose eq1901 eq5812
    | exact resolve eq5812 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901 eq5812
  have eq5951 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5897
       have i₂ := eq539 sF3 y sF3
       grind)
    | exact superpose eq539 eq5897
    | exact resolve eq5897 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5897
  have eq5985 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op x (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5951
       have i₂ := eq539 sF4 sF2 x
       grind)
    | exact superpose eq539 eq5951
    | exact resolve eq5951 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5951
  have eq6003 : (M.op (σ y) (σ x)) = (M.op x (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1044 eq5985
    | exact resolve eq5985 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5985
  have eq6011 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5442 eq6003
    | exact resolve eq6003 eq5442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003
  have eq6646 : (M.op (σ x) (σ y)) = (M.op (σ (M.op y (M.op y x))) (σ y)) := by
    first
    | (have i₁ := eq5478 (M.op x x)
       have i₂ := eq2735 x x
       grind)
    | exact superpose eq2735 eq5478
    | exact resolve eq5478 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5478
  have eq6706 : (M.op (σ x) (σ y)) = (M.op (σ (M.op y (M.op x (M.op x y)))) (σ y)) := by
    first
    | (have i₁ := eq6646
       have i₂ := eq2544
       grind)
    | exact superpose eq2544 eq6646
    | exact resolve eq6646 eq2544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544 eq6646
  have eq7198 : (M.op x y) = (M.op (M.op y (M.op x (M.op x y))) y) := by
    first
    | exact superpose eq4207 eq531
    | exact resolve eq531 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4207
  have eq7204 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op y (M.op y X0)) (M.op (M.op x x) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq531 (M.op x x) X0
       have i₂ := eq2735 X0 x
       grind)
    | exact superpose eq2735 eq531
    | exact resolve eq531 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq2735
  have eq7484 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op (M.op x x) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq7204 X0
       have i₂ := eq539 (M.op (M.op x x) X0) y X0
       grind)
    | exact superpose eq539 eq7204
    | exact resolve eq7204 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7204
  have eq7551 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq7484 X0
       have i₂ := eq1904 X0
       grind)
    | exact superpose eq1904 eq7484
    | exact resolve eq7484 eq1904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904 eq7484
  have eq8098 : ∀ X0 X1 : G, (M.op (M.op y (M.op y X0)) X1) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X1 x (M.op y (M.op y X0))
       have i₂ := eq2460 X0
       grind)
    | exact superpose eq2460 eq539
    | exact resolve eq539 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8100 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op (M.op y (M.op y X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq680 X1 x (M.op y (M.op y X0))
       have i₂ := eq2460 X0
       grind)
    | exact superpose eq2460 eq680
    | exact resolve eq680 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8101 : ∀ X0 X1 : G, (M.op x (M.op (M.op y (M.op y X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq685 (M.op y (M.op y X0)) x X1
       have i₂ := eq2460 X0
       grind)
    | exact superpose eq2460 eq685
    | exact resolve eq685 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460
  have eq8105 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8101 X0 X1
       have i₂ := eq539 (M.op X0 X1) y X0
       grind)
    | exact superpose eq539 eq8101
    | exact resolve eq8101 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8101
  have eq8106 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8100 X0 X1
       have i₂ := eq539 X1 y X0
       grind)
    | exact superpose eq539 eq8100
    | exact resolve eq8100 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8100
  have eq8107 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8098 X0 X1
       have i₂ := eq539 X1 y X0
       grind)
    | exact superpose eq539 eq8098
    | exact resolve eq8098 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq8098
  have eq8500 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2890 X1 (M.op (M.op X1 x) X0)
       have i₂ := eq685 x X1 X0
       grind)
    | exact superpose eq685 eq2890
    | exact resolve eq2890 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8538 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq680 (M.op x X0) X1 X1
       have i₂ := eq2890 X1 X0
       grind)
    | exact superpose eq2890 eq680
    | exact resolve eq680 eq2890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9310 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq3528 (M.op x x)
       have i₂ := eq2890 sF3 x
       grind)
    | exact superpose eq2890 eq3528
    | exact resolve eq3528 eq2890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528
  have eq10880 : (M.op x y) ≠ (M.op y (M.op y (M.op x (M.op x y)))) ∨ (M.op x y) = (k (M.op y (M.op x (M.op x y))) y) := by
    first
    | exact superpose eq7198 eq13
    | exact resolve eq13 eq7198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7198
  have eq10916 : (M.op x y) = (k (M.op y (M.op x (M.op x y))) y) := by
    first
    | (have r₁ := eq10880
       have r₂ := eq2844 (M.op x y)
       grind)
    | exact resolve eq10880 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844 eq10880
  have eq11315 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq1044 eq217
    | (have j0 := eq217 X0
       grind)
    | exact resolve eq217 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq27671 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (σ y)) (M.op (M.op (M.op x X0) (M.op (σ x) (σ y))) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq9310 eq508
    | exact resolve eq508 eq9310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq9310
  have eq27672 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (σ y)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27671 X0 X1 X2
       have i₂ := eq8107 X0 sF4
       grind)
    | exact superpose eq8107 eq27671
    | exact resolve eq27671 eq8107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27671
  have eq28303 : (σ (M.op x y)) = (M.op (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) (σ y)) (σ y)) := by
    first
    | exact superpose eq1538 eq27672
    | exact resolve eq27672 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq27672
  have eq28418 : (σ (M.op x y)) = (M.op (M.op (M.op x (σ (M.op x y))) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq28303
       have i₂ := eq8538 sF1 sF1
       grind)
    | exact superpose eq8538 eq28303
    | exact resolve eq28303 eq8538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28303
  have eq28711 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq28418
       have i₂ := eq8107 sF1 sF3
       grind)
    | exact superpose eq8107 eq28418
    | exact resolve eq28418 eq8107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28418
  have eq29126 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (M.op x (σ (M.op x y)))) := by
    first
    | exact superpose eq28711 eq8106
    | exact resolve eq8106 eq28711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8106 eq28711
  have eq52590 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X2) (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4460 eq678
    | exact resolve eq678 eq4460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq4460
  have eq138293 : (M.op x (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq29126 eq685
    | exact resolve eq685 eq29126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29126
  have eq138583 : (M.op (σ (M.op x y)) (σ x)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq1044 eq138293
    | exact resolve eq138293 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138293
  have eq142833 : (σ x) = (M.op x (M.op (σ (M.op x y)) (M.op x (σ (M.op x y))))) := by
    first
    | exact superpose eq138583 eq8105
    | exact resolve eq8105 eq138583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8105 eq138583
  have eq169816 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X1) (M.op X0 (M.op X0 X0)))) = X0 ∨ (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1007 X0 X1
       have i₂ := eq8538 X1 X0
       grind)
    | exact superpose eq8538 eq1007
    | (have j0 := eq1007 X0 X1
       grind)
    | exact resolve eq1007 eq8538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq8538
  have eq169817 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) = X0 ∨ (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq169816 X0 X1
       have i₂ := eq8107 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq8107 eq169816
    | (have j0 := eq169816 X0 X1
       grind)
    | exact resolve eq169816 eq8107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169816
  have eq169977 : y = (M.op (M.op y (M.op x y)) y) ∨ y = (M.op y (k (M.op y y) y)) := by
    first
    | (have i₁ := eq169817 y (M.op y (M.op x y))
       have i₂ := eq3172 y y
       grind)
    | exact superpose eq3172 eq169817
    | (have j0 := eq169817 y x
       grind)
    | exact resolve eq169817 eq3172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3172 eq169817
  have eq170589 : y = (M.op x y) ∨ y = (M.op y (k (M.op y y) y)) := by
    first
    | (have i₁ := eq169977
       have i₂ := eq7551 y
       grind)
    | exact superpose eq7551 eq169977
    | exact resolve eq169977 eq7551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7551 eq169977
  have eq170765 : y = (M.op y (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq170589
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq170589
    | exact resolve eq170589 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996 eq170589
  have eq306337 : ∀ X0 : G, (M.op (M.op x (M.op X0 x)) (σ x)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq142833 eq675
    | exact resolve eq675 eq142833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq142833
  have eq306773 : ∀ X0 : G, (M.op (M.op X0 x) (σ x)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq306337 X0
       have i₂ := eq8107 (M.op X0 x) sF2
       grind)
    | exact superpose eq8107 eq306337
    | exact resolve eq306337 eq8107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8107 eq306337
  have eq306943 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq306773 x
       have i₂ := eq8500 sF2 x
       grind)
    | exact superpose eq8500 eq306773
    | exact resolve eq306773 eq8500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8500 eq306773
  have eq360707 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ (M.op x y)) (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq306943 eq685
    | exact resolve eq685 eq306943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq306943
  have eq381864 : ∀ X0 : G, (M.op (k x y) y) = (M.op (M.op X0 y) (M.op X0 (M.op y (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq52590 X0 y (k x y)
       have i₂ := eq170765
       grind)
    | exact superpose eq170765 eq52590
    | exact resolve eq52590 eq170765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52590 eq170765
  have eq381918 : (M.op x y) = (M.op (k x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq381864 x
       have i₂ := eq680 sF0 x y
       grind)
    | exact superpose eq680 eq381864
    | exact resolve eq381864 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq381864
  have eq382474 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq5442 eq360707
    | exact resolve eq360707 eq5442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5442 eq360707
  have eq383256 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op x (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq6011 eq382474
    | exact resolve eq382474 eq6011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6011 eq382474
  have eq412902 : (M.op (σ x) (σ y)) = (σ (k (M.op y (M.op x (M.op x y))) y)) ∨ (σ x) = (σ (M.op y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq6706 eq11315
    | (have j0 := eq11315 (M.op y (M.op x (M.op x y)))
       grind)
    | exact resolve eq11315 eq6706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11315
  have eq413405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq10916 eq412902
    | exact resolve eq412902 eq10916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412902
  have eq413517 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq21 eq413405
    | exact resolve eq413405 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413405
  have eq413595 : (σ x) = (σ (M.op y (M.op x (M.op x y)))) := by
    first
    | (have r₁ := eq413517
       have r₂ := eq28
       grind)
    | exact resolve eq413517 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413517
  have eq413742 : (k (σ x) (σ y)) = (σ (k (M.op y (M.op x (M.op x y))) y)) := by
    first
    | exact superpose eq413595 eq41
    | exact resolve eq41 eq413595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq413595
  have eq413814 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq10916 eq413742
    | exact resolve eq413742 eq10916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10916 eq413742
  have eq413833 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq413814
    | exact resolve eq413814 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413814
  have eq413846 : (τ (σ (M.op x y))) = (k x y) := by
    first
    | exact superpose eq413833 eq60
    | exact resolve eq60 eq413833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq413833
  have eq413867 : (M.op x y) = (k x y) := by
    first
    | exact superpose eq31 eq413846
    | exact resolve eq413846 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq413846
  have eq413917 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq381918
       have i₂ := eq413867
       grind)
    | exact superpose eq413867 eq381918
    | exact resolve eq381918 eq413867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381918 eq413867
  have eq413941 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1742 eq413917
    | exact resolve eq413917 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742 eq413917
  have eq414072 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq413941 eq21
    | exact resolve eq21 eq413941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413941
  have eq414207 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq414072
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq414072
    | exact resolve eq414072 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414072
  have eq414400 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq414207 eq383256
    | exact resolve eq383256 eq414207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383256 eq414207
  have eq414405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq414400
       have i₂ := eq2890 sF1 sF4
       grind)
    | (have i₁ := eq414400
       have i₂ := eq2890 x (M.op sF1 (M.op sF1 (M.op x sF4)))
       grind)
    | exact superpose eq2890 eq414400
    | exact resolve eq414400 eq2890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890 eq414400
  have eq414496 : x = (M.op x y) := by
    first
    | (have r₁ := eq414405
       have r₂ := eq28
       grind)
    | exact resolve eq414405 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414405
  have eq414577 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq414496 eq21
    | exact resolve eq21 eq414496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq414628 : (M.op (σ x) (σ y)) = (M.op (σ (M.op y (M.op x x))) (σ y)) := by
    first
    | exact superpose eq414496 eq6706
    | exact resolve eq6706 eq414496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6706 eq414496
  have eq414688 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq414628
       have i₂ := eq1067
       grind)
    | exact superpose eq1067 eq414628
    | exact resolve eq414628 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067 eq414628
  have eq414726 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq414577
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq414577
    | exact resolve eq414577 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq414577
  have eq414735 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq414688
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq414688
    | exact resolve eq414688 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq414688
  have eq414753 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1044 eq414735
    | exact resolve eq414735 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq414735
  have eq414973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq414726 eq414753
    | exact resolve eq414753 eq414726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414726 eq414753
  have eq414974 : False := by grind
  exact eq414974
