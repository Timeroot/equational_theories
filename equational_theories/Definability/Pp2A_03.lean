import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq279 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq266
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq266
    | exact resolve eq266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq282 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq273 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq282 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq282 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq282 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq294 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq283 (σ X0)
       grind)
    | exact superpose eq283 eq15
    | exact resolve eq15 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq294 X0
       have i₂ := eq283 X0
       grind)
    | exact superpose eq283 eq294
    | exact resolve eq294 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq294
  have eq588 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq274 (σ X0) X1
       grind)
    | exact superpose eq274 eq22
    | (have j1 := eq274 (σ X0) X1
       grind)
    | exact resolve eq22 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq274 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3851 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq588 X0 X1
       grind)
    | exact superpose eq588 eq22
    | (have j1 := eq588 X0 X1
       grind)
    | exact resolve eq22 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3863 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (σ X0)
       have i₂ := eq588 X0 (σ X1)
       grind)
    | exact superpose eq588 eq28
    | (have j1 := eq588 X0 (σ X1)
       grind)
    | exact resolve eq28 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq3896 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3863 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3863
    | (have j0 := eq3863 X0 X1
       grind)
    | exact resolve eq3863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863
  have eq3908 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3851 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3851
    | (have j0 := eq3851 X0 X1
       grind)
    | exact resolve eq3851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851
  have eq3920 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3896 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3896
    | (have j0 := eq3896 X0 X1
       grind)
    | exact resolve eq3896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq4106 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (M.op (σ (τ X1)) X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3908 (τ X0) X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq3908
    | (have j0 := eq3908 (τ X1) X0
       grind)
    | exact resolve eq3908 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3908
  have eq4217 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4106 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4106
    | (have j0 := eq4106 X0 X1
       grind)
    | exact resolve eq4106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106
  have eq4258 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4217 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4217
    | (have j0 := eq4217 X0 X1
       grind)
    | exact resolve eq4217 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217
  have eq4392 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq4258 X1 X0
       grind)
    | exact superpose eq4258 eq11
    | (have j1 := eq4258 X1 X0
       grind)
    | exact resolve eq11 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4258
  have eq4512 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4392 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4392
    | (have j0 := eq4392 X0 X1
       grind)
    | exact resolve eq4392 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4392
  have eq4625 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq4512 X0 (σ X1)
       grind)
    | exact superpose eq4512 eq28
    | (have j1 := eq4512 X0 (σ X1)
       grind)
    | exact resolve eq28 eq4512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4512
  have eq5824 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq3920 X0 X1
       grind)
    | exact superpose eq3920 eq12
    | (have j1 := eq3920 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq3920 X1 X1
       grind)
    | exact resolve eq12 eq3920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5825 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq3920 X0 X1
       grind)
    | exact superpose eq3920 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq3920 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq3920 X0 X1
       grind)
    | exact resolve eq13 eq3920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920
  have eq5829 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5825 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5825
  have eq5836 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5829 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5829
    | (have j0 := eq5829 X0 X1
       grind)
    | exact resolve eq5829 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5829
  have eq5837 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) ≠ (σ X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5824 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5824
    | (have j0 := eq5824 X0 X1
       grind)
    | exact resolve eq5824 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5824
  have eq5866 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5837 X0 X1
       have j1 := eq5836 X0 X1
       grind)
    | (have r₁ := eq5837 X0 (k X0 X1)
       have r₂ := eq5836 X0 X1
       grind)
    | (have r₁ := eq5837 (k X0 X1) X0
       have r₂ := eq5836 X0 X1
       grind)
    | (have r₁ := eq5837 X0 X1
       have r₂ := eq5836 X0 X1
       grind)
    | exact resolve eq5837 eq5836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5836 eq5837
  have eq6030 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq5866 X0 X1
       grind)
    | exact superpose eq5866 eq10
    | (have j1 := eq5866 X0 X1
       grind)
    | exact resolve eq10 eq5866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5866
  have eq6081 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6030 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6030
    | (have j0 := eq6030 X0 X1
       grind)
    | exact resolve eq6030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6030
  have eq6272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq6081 X0 X1
       grind)
    | exact superpose eq6081 eq11
    | (have j1 := eq6081 X0 X1
       grind)
    | exact resolve eq11 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6081
  have eq6423 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6272 y x
       grind)
    | exact superpose eq6272 eq16
    | (have j1 := eq6272 y x
       grind)
    | exact resolve eq16 eq6272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6272
  have eq6551 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq6423
       have i₂ := eq274 x y
       grind)
    | exact superpose eq274 eq6423
    | (have j1 := eq274 x y
       grind)
    | exact resolve eq6423 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq6423
  have eq6557 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq6551
  have eq6558 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq6557
  have eq6559 : y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have j1 := eq606 y x
       grind)
    | (have r₁ := eq6558
       have r₂ := eq606 y x
       grind)
    | exact resolve eq6558 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq6558
  have eq6563 : x ≠ y ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6559
       grind)
    | exact superpose eq6559 eq12
    | exact resolve eq12 eq6559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6564 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6559
       grind)
    | exact superpose eq6559 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6559
       grind)
    | exact resolve eq13 eq6559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6568 : x = y ∨ y = (k y x) ∨ x = (k y x) := by grind
  clear eq6564
  have eq6571 : y = (k y x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq6563
       have r₂ := eq6568
       grind)
    | exact resolve eq6563 eq6568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6563 eq6568
  have eq6584 : x ≠ y ∨ x = (k y x) := by grind
  have eq6600 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq279
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq279
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq279 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6601 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq6600
  have eq17492 : (σ (M.op x y)) ≠ (σ y) ∨ (τ (σ x)) = (k y (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4625 (σ x) y
       grind)
    | exact superpose eq4625 eq16
    | (have j1 := eq4625 (σ x) y
       grind)
    | exact resolve eq16 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4625
  have eq17529 : x = (k y x) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq17492
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17492
    | exact resolve eq17492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17492
  have eq17549 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq17529
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17529
    | exact resolve eq17529 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17529
  have eq17587 : (σ y) ≠ (σ y) ∨ x = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq17549
       have i₂ := eq6559
       grind)
    | exact superpose eq6559 eq17549
    | exact resolve eq17549 eq6559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17549
  have eq17592 : (σ y) ≠ (σ y) ∨ x = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq17587
  have eq17593 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y x) := by grind
  clear eq17592
  have eq17602 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17593
       grind)
    | exact superpose eq17593 eq16
    | exact resolve eq16 eq17593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17593
  have eq17682 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq17602
       have i₂ := eq6571
       grind)
    | exact superpose eq6571 eq17602
    | exact resolve eq17602 eq6571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6571 eq17602
  have eq17695 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq17682
       have r₂ := eq6584
       grind)
    | exact resolve eq17682 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6584 eq17682
  have eq17698 : (σ y) ≠ (σ y) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq17695
       have i₂ := eq6559
       grind)
    | exact superpose eq6559 eq17695
    | exact resolve eq17695 eq6559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6559 eq17695
  have eq17703 : (σ y) ≠ (σ y) ∨ x = (k y x) := by grind
  clear eq17698
  have eq17704 : x = (k y x) := by grind
  clear eq17703
  have eq140127 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6601
       grind)
    | exact superpose eq6601 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6601
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6601
       grind)
    | exact resolve eq13 eq6601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6601
  have eq140166 : x = y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq140127
  have eq140182 : x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq140166
       have i₂ := eq17704
       grind)
    | exact superpose eq17704 eq140166
    | exact resolve eq140166 eq17704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140166
  have eq140183 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq140182
  have eq140196 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq140183
       have i₂ := eq17704
       grind)
    | exact superpose eq17704 eq140183
    | exact resolve eq140183 eq17704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140183
  have eq140200 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140196
       have i₂ := eq17704
       grind)
    | exact superpose eq17704 eq140196
    | exact resolve eq140196 eq17704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140196
  have eq140201 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140200
       grind)
    | exact superpose eq140200 eq16
    | exact resolve eq16 eq140200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140200
  have eq140283 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq140201
       have r₂ := eq313 x
       grind)
    | exact resolve eq140201 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq140201
  have eq140304 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq279
       have i₂ := eq140283
       grind)
    | exact superpose eq140283 eq279
    | exact resolve eq279 eq140283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq140283
  have eq140375 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq140304
  have eq140376 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq140375
  have eq140383 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140376
       have i₂ := eq17704
       grind)
    | exact superpose eq17704 eq140376
    | exact resolve eq140376 eq17704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140376
  have eq140384 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq140383
  have eq140434 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq140384
       grind)
    | exact superpose eq140384 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq140384
       grind)
    | exact resolve eq13 eq140384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140462 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq140384
  have eq140470 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq140434
  have eq140508 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq140470
       have r₂ := eq140462
       grind)
    | exact resolve eq140470 eq140462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140470
  have eq140553 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140508
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq140508
    | exact resolve eq140508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140508
  have eq140592 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140553
       have i₂ := eq17704
       grind)
    | exact superpose eq17704 eq140553
    | exact resolve eq140553 eq17704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140553
  have eq140620 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq140592
       have r₂ := eq140462
       grind)
    | exact resolve eq140592 eq140462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140462 eq140592
  have eq140687 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140620
       grind)
    | exact superpose eq140620 eq16
    | exact resolve eq16 eq140620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140620
  have eq141009 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq140687
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq140687
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq140687 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141018 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq141009
  have eq141020 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq141018
       have i₂ := eq17704
       grind)
    | exact superpose eq17704 eq141018
    | exact resolve eq141018 eq17704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141018
  have eq141040 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq141020
       grind)
    | exact superpose eq141020 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq141020
       grind)
    | exact resolve eq13 eq141020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141068 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq141020
  have eq141076 : x = y ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq141040
  have eq141091 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq141076
       have r₂ := eq141068
       grind)
    | exact resolve eq141076 eq141068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141076
  have eq141095 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq141091
       have i₂ := eq17704
       grind)
    | exact superpose eq17704 eq141091
    | exact resolve eq141091 eq17704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17704 eq141091
  have eq141097 : x = (M.op x y) := by
    first
    | (have r₁ := eq141095
       have r₂ := eq141068
       grind)
    | exact resolve eq141095 eq141068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141068 eq141095
  have eq141126 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq140687
       have i₂ := eq141097
       grind)
    | exact superpose eq141097 eq140687
    | exact resolve eq140687 eq141097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140687 eq141097
  have eq141181 : False := by grind
  exact eq141181

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pyx_Equation1437 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq596 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq587
    | (have j0 := eq587 X0 X1
       grind)
    | exact resolve eq587 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq587
  have eq604 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq579 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq579
    | (have j0 := eq579 X0 X1
       grind)
    | exact resolve eq579 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq618 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq604 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq604
    | (have j0 := eq604 X0 X1
       grind)
    | exact resolve eq604 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq686 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op (M.op X3 X2) (M.op X3 X2)) (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X3 X2) X4 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq110 X2 X0 X1 X3
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq781 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op X3 (M.op X4 (M.op X5 (M.op X1 (M.op X2 X0)))))) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq686 X0 X1 (M.op X1 (M.op X2 X0)) (M.op X0 X0) X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq686
    | exact resolve eq686 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op X0 X0) (M.op X6 (M.op X7 (M.op X8 (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 X0))))))))) = X0 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq686 X0 X1 (M.op X3 (M.op X4 (M.op X5 (M.op X1 (M.op X2 X0))))) (M.op X0 X0) X4
       have i₂ := eq781 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq781 eq686
    | exact resolve eq686 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq781
  have eq3179 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq618 x y
       grind)
    | exact superpose eq618 eq16
    | (have j1 := eq618 x y
       grind)
    | exact resolve eq16 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq4358 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq596 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq596
    | (have j0 := eq596 X1 (σ X0)
       grind)
    | exact resolve eq596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq4415 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4358 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4358
    | (have j0 := eq4358 X0 X1
       grind)
    | exact resolve eq4358 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4358
  have eq4424 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4415 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq4415
    | (have j0 := eq4415 X0 X1
       grind)
    | exact resolve eq4415 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4415
  have eq4429 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4424 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4424
    | (have j0 := eq4424 X0 X1
       grind)
    | exact resolve eq4424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4424
  have eq6049 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3179
       have i₂ := eq4429 y x
       grind)
    | exact superpose eq4429 eq3179
    | (have j1 := eq4429 x y
       grind)
    | (have r₁ := eq3179
       have r₂ := eq4429 y x
       grind)
    | (have r₁ := eq3179
       have r₂ := eq4429 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3179
       have r₂ := eq4429 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3179 eq4429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3179 eq4429
  have eq6050 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq6049
  have eq11314 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6050
       grind)
    | exact superpose eq6050 eq16
    | exact resolve eq16 eq6050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050
  have eq11315 : (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq11314
       have r₂ := eq22 x
       grind)
    | exact resolve eq11314 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11314
  have eq11320 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq11315
       grind)
    | exact superpose eq11315 eq22
    | exact resolve eq22 eq11315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11315
  have eq11375 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11320
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq11320
    | exact resolve eq11320 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11320
  have eq11376 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq11375
  have eq11403 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq11376
       grind)
    | exact superpose eq11376 eq10
    | exact resolve eq10 eq11376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11376
  have eq11464 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq11403
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq11403
    | exact resolve eq11403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11403
  have eq11465 : (M.op x x) = (M.op y y) := by grind
  clear eq11464
  have eq11540 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, y = (M.op (M.op x x) (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op X6 (M.op x x))))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq903 y X1 X2 X3 X4 y X6 x x
       have i₂ := eq11465
       grind)
    | exact superpose eq11465 eq903
    | exact resolve eq903 eq11465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11465
  have eq11541 : x = y := by
    first
    | (have i₁ := eq11540 x x x x x x x
       have i₂ := eq903 x x x x x x x x x
       grind)
    | exact superpose eq903 eq11540
    | exact resolve eq11540 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq11540
  have eq11564 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11541
       grind)
    | exact superpose eq11541 eq16
    | exact resolve eq16 eq11541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11541
  have eq11565 : False := by grind
  exact eq11565

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pyx_Equation1437 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq97 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq100 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq99
    | (have j0 := eq99 X0 X1
       grind)
    | exact resolve eq99 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq99
  have eq102 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq106 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq102
    | (have j0 := eq102 X0 X1
       grind)
    | exact resolve eq102 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq202 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op (M.op X3 X2) (M.op X3 X2)) (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X3 X2) X4 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq42 X2 X0 X1 X3
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq249 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106 x y
       grind)
    | exact superpose eq106 eq16
    | (have j1 := eq106 x y
       grind)
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq720 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op X3 (M.op X4 (M.op X5 (M.op X1 (M.op X2 X0)))))) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq202 X0 X1 (M.op X1 (M.op X2 X0)) (M.op X0 X0) X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq202
    | exact resolve eq202 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 X2 X3 X4 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) (M.op X2 (M.op X3 (M.op X4 (M.op X1 (σ (M.op X0 X0))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq202 X0 X1 (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0)) X4
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq202
    | exact resolve eq202 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq775 : ∀ X0 X1 X2 X3 X4 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X2 (M.op X3 (M.op X4 (M.op X1 (σ (M.op X0 X0))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq729 X0 X1 X2 X3 X4
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq729
    | exact resolve eq729 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq964 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op X0 X0) (M.op X6 (M.op X7 (M.op X8 (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 X0))))))))) = X0 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq202 X0 X1 (M.op X3 (M.op X4 (M.op X5 (M.op X1 (M.op X2 X0))))) (M.op X0 X0) X4
       have i₂ := eq720 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq720 eq202
    | exact resolve eq202 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq720
  have eq1352 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | (have j0 := eq100 X1 (σ X0)
       grind)
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1399 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1352 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1352
    | (have j0 := eq1352 X0 X1
       grind)
    | exact resolve eq1352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1405 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1399 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1399
    | (have j0 := eq1399 X0 X1
       grind)
    | exact resolve eq1399 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1409 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1405 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1405
    | (have j0 := eq1405 X0 X1
       grind)
    | exact resolve eq1405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1756 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq249
       have i₂ := eq1409 y x
       grind)
    | exact superpose eq1409 eq249
    | (have j1 := eq1409 x y
       grind)
    | (have r₁ := eq249
       have r₂ := eq1409 y x
       grind)
    | (have r₁ := eq249
       have r₂ := eq1409 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq249
       have r₂ := eq1409 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq249 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq1409
  have eq1757 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq1756
  have eq18148 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1757
       grind)
    | exact superpose eq1757 eq16
    | exact resolve eq16 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq18149 : (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq18148
       have r₂ := eq22 x
       grind)
    | exact resolve eq18148 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18148
  have eq18154 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq18149
       grind)
    | exact superpose eq18149 eq22
    | exact resolve eq22 eq18149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18149
  have eq18249 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq18154
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq18154
    | exact resolve eq18154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18154
  have eq18250 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq18249
  have eq18554 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, y = (M.op (M.op x x) (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op X6 (M.op x x))))))))) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq964 y X1 X2 X3 X4 y X6 x x
       have i₂ := eq18250
       grind)
    | exact superpose eq18250 eq964
    | exact resolve eq964 eq18250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18250
  have eq18555 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq18554 x x x x x x x
       have i₂ := eq964 x x x x x x x x x
       grind)
    | exact superpose eq964 eq18554
    | exact resolve eq18554 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq18554
  have eq18578 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18555
       grind)
    | exact superpose eq18555 eq16
    | exact resolve eq16 eq18555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18555
  have eq18579 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq18578
       have r₂ := eq22 x
       grind)
    | exact resolve eq18578 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18578
  have eq18819 : ∀ X0 X1 X2 X3 : G, (σ y) = (M.op (σ (M.op x x)) (M.op X0 (M.op X1 (M.op X2 (M.op X3 (σ (M.op x x))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq775 y X1 X2 X3 x
       have i₂ := eq18579
       grind)
    | exact superpose eq18579 eq775
    | exact resolve eq775 eq18579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18579
  have eq18934 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18819 x x x x
       have i₂ := eq775 x x x x x
       grind)
    | exact superpose eq775 eq18819
    | exact resolve eq18819 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq18819
  have eq18937 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18934
       grind)
    | exact superpose eq18934 eq16
    | exact resolve eq16 eq18934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18938 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18934
       grind)
    | exact superpose eq18934 eq10
    | exact resolve eq10 eq18934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18934
  have eq19071 : x = y := by
    first
    | (have i₁ := eq18938
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18938
    | exact resolve eq18938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18938
  have eq19072 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18937
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq18937
    | exact resolve eq18937 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18937
  have eq19077 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq19072
       have i₂ := eq19071
       grind)
    | exact superpose eq19071 eq19072
    | exact resolve eq19072 eq19071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19071 eq19072
  have eq19078 : False := by grind
  exact eq19078

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pyx_pxy_Equation1443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 x)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X2 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X1 x
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
  clear eq19
  have eq34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq40 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq71 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq80 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) X1)))) = (σ (M.op (τ X0) (M.op (τ X0) (M.op (τ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (M.op (τ X0) X1))
       have i₂ := eq34 (τ X0) X1
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq4645 : ∀ X0 X1 : G, (M.op (σ X1) (M.op X0 (σ X1))) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (σ X0) X1
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq71
    | (have j1 := eq82 X1 X0
       grind)
    | exact resolve eq71 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4656 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq82 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq4657 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4656 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4656
  have eq4661 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4657 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4657
    | (have j0 := eq4657 X0
       grind)
    | exact resolve eq4657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq4701 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq4661 X0
       grind)
    | exact superpose eq4661 eq40
    | (have j1 := eq4661 X0
       grind)
    | exact resolve eq40 eq4661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4661
  have eq4719 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4701 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4701
    | (have j0 := eq4701 X0
       grind)
    | exact resolve eq4701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4701
  have eq4720 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4719 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4722 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4720 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4720
    | exact resolve eq4720 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4749 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4720 X0
       grind)
    | exact superpose eq4720 eq11
    | exact resolve eq11 eq4720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4720
  have eq4810 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4722 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq4722
    | exact resolve eq4722 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4722
  have eq4977 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4810 X0
       grind)
    | exact superpose eq4810 eq11
    | exact resolve eq11 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5088 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4977 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4977
    | exact resolve eq4977 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4977
  have eq5153 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq5088 (τ X0)
       grind)
    | exact superpose eq5088 eq36
    | exact resolve eq36 eq5088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5208 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5153 X0
       have i₂ := eq4810 X0
       grind)
    | exact superpose eq4810 eq5153
    | exact resolve eq5153 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810 eq5153
  have eq5841 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5849 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq71 (σ X0) (σ X0)
       have i₂ := eq4749 X0
       grind)
    | exact superpose eq4749 eq71
    | exact resolve eq71 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5862 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5849 X0
       have i₂ := eq5088 X0
       grind)
    | exact superpose eq5088 eq5849
    | exact resolve eq5849 eq5088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5849
  have eq5869 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5841 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5841
    | exact resolve eq5841 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5841
  have eq5904 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5869 X0
       have i₂ := eq5088 X0
       grind)
    | exact superpose eq5088 eq5869
    | exact resolve eq5869 eq5088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5869
  have eq5922 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5904
  have eq7153 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) ∨ (τ (M.op (M.op (σ X0) X1) (σ X0))) = (k (τ (M.op (σ X0) X1)) X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (σ X0) X1
       have i₂ := eq80 (M.op (σ X0) X1) X0
       grind)
    | exact superpose eq80 eq71
    | (have j1 := eq80 (M.op (σ X0) X1) X0
       grind)
    | exact resolve eq71 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq80
  have eq7170 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) ∨ (τ (M.op (M.op (σ X0) X1) (σ X0))) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq7153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7153
  have eq7188 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (k X0 X0)) ∨ (τ (M.op (M.op (σ X0) X1) (σ X0))) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7170 X0 X1
       have i₂ := eq4749 X0
       grind)
    | exact superpose eq4749 eq7170
    | (have j0 := eq7170 X0 X1
       grind)
    | exact resolve eq7170 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7170
  have eq7222 : ∀ X0 X1 : G, (τ (M.op (M.op (σ X0) X1) (σ X0))) = (k (τ (M.op (σ X0) X1)) X0) ∨ (M.op (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7188 X0 X1
       have i₂ := eq5088 X0
       grind)
    | exact superpose eq5088 eq7188
    | (have j0 := eq7188 X0 X1
       grind)
    | exact resolve eq7188 eq5088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7188
  have eq7542 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5922 (σ X0)
       have i₂ := eq4749 X0
       grind)
    | exact superpose eq4749 eq5922
    | exact resolve eq5922 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7634 : ∀ X0 : G, (σ (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7542 X0
       have i₂ := eq5088 X0
       grind)
    | exact superpose eq5088 eq7542
    | exact resolve eq7542 eq5088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7542
  have eq7652 : ∀ X0 : G, (σ (σ (M.op (M.op X0 X0) X0))) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7634 X0
       have i₂ := eq5922 X0
       grind)
    | exact superpose eq5922 eq7634
    | exact resolve eq7634 eq5922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7634
  have eq9874 : ∀ X0 : G, (σ (σ (k X0 X0))) = (M.op (σ (σ X0)) (M.op (σ (σ (k X0 X0))) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq5862 (σ X0)
       have i₂ := eq4749 X0
       grind)
    | exact superpose eq4749 eq5862
    | exact resolve eq5862 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5862
  have eq9971 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X0)) (M.op (σ (σ (M.op X0 X0))) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq9874 X0
       have i₂ := eq5088 X0
       grind)
    | exact superpose eq5088 eq9874
    | exact resolve eq9874 eq5088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9874
  have eq9992 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X0)) (σ (σ (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq9971 X0
       have i₂ := eq7652 X0
       grind)
    | exact superpose eq7652 eq9971
    | exact resolve eq9971 eq7652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9971
  have eq12409 : ∀ X0 X1 : G, (σ (σ (M.op X0 (M.op X0 (M.op X0 X1))))) = (M.op (σ (σ X0)) (σ (σ (M.op X0 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq7652 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 (M.op X0 x) x
       grind)
    | exact superpose eq9 eq7652
    | exact resolve eq7652 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7652
  have eq12875 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op (σ (σ (M.op X0 (M.op X0 X1)))) (σ (σ (M.op X0 (M.op X0 (M.op X0 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9992 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 (M.op X0 x) x
       grind)
    | exact superpose eq9 eq9992
    | exact resolve eq9992 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9992
  have eq83444 : ∀ X0 X1 X2 : G, (σ (σ X0)) = (M.op (M.op (σ (σ X0)) X2) (M.op (σ (σ X0)) (σ (σ (M.op X0 (M.op X0 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ (σ (M.op X0 (M.op X0 X1)))) (σ (σ (M.op X0 (M.op X0 (M.op X0 X1))))) X2
       have i₂ := eq12875 X0 X1
       grind)
    | exact superpose eq12875 eq21
    | exact resolve eq21 eq12875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq12875
  have eq83543 : ∀ X0 X1 X2 : G, (σ (σ X0)) = (M.op (M.op (σ (σ X0)) X2) (σ (σ (M.op X0 (M.op X0 (M.op X0 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83444 X0 X1 X2
       have i₂ := eq12409 X0 X1
       grind)
    | exact superpose eq12409 eq83444
    | exact resolve eq83444 eq12409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12409 eq83444
  have eq84790 : ∀ X0 X1 X2 : G, (σ (σ (τ X0))) = (M.op (M.op (σ (σ (τ X0))) X2) (σ (k X0 (σ (M.op (τ X0) (M.op (τ X0) X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83543 (τ X0) X1 X2
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq83543
    | exact resolve eq83543 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83543
  have eq84876 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X2) (σ (k X0 (σ (M.op (τ X0) (M.op (τ X0) X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84790 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84790
    | exact resolve eq84790 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84790
  have eq86848 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X0)) X2) (k X0 (σ (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84876 (τ X0) X1 X2
       have i₂ := eq18 X0 (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)))
       grind)
    | exact superpose eq18 eq84876
    | exact resolve eq84876 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84876
  have eq86959 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (k X0 (σ (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86848 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86848
    | exact resolve eq86848 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86848
  have eq91500 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (k X0 (σ (k (τ X0) (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86959 X0 (M.op (τ (τ X0)) X1) X2
       have i₂ := eq115 (τ X0) X1
       grind)
    | exact superpose eq115 eq86959
    | exact resolve eq86959 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86959
  have eq91600 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (k X0 (k X0 (σ (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91500 X0 X1 X2
       have i₂ := eq18 X0 (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)))
       grind)
    | exact superpose eq18 eq91500
    | exact resolve eq91500 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91500
  have eq231399 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (k X0 (k X0 (σ (k (τ X0) (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91600 X0 (M.op (τ (τ X0)) X1) X2
       have i₂ := eq115 (τ X0) X1
       grind)
    | exact superpose eq115 eq91600
    | exact resolve eq91600 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq91600
  have eq231528 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (k X0 (k X0 (k X0 (σ (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231399 X0 X1 X2
       have i₂ := eq18 X0 (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)))
       grind)
    | exact superpose eq18 eq231399
    | exact resolve eq231399 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231399
  have eq1511542 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X1) X0)) = (k (τ (M.op X0 X1)) (τ X0)) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7222 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7222
    | exact resolve eq7222 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7222
  have eq1512449 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X1) X0)) = (τ (k (M.op X0 X1) X0)) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1511542 X0 X1
       have i₂ := eq36 X0 (M.op X0 X1)
       grind)
    | exact superpose eq36 eq1511542
    | (have j0 := eq1511542 X0 X1
       grind)
    | exact resolve eq1511542 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511542
  have eq1512798 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (τ (M.op (M.op X0 X1) X0)) = (τ (k (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1512449 X0 X1
       have i₂ := eq5208 X0
       grind)
    | exact superpose eq5208 eq1512449
    | (have j0 := eq1512449 X0 X1
       grind)
    | exact resolve eq1512449 eq5208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5208 eq1512449
  have eq1513003 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X1) X0)) = (τ (k (M.op X0 X1) X0)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1512798 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1512798
    | (have j0 := eq1512798 X0 X1
       grind)
    | exact resolve eq1512798 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512798
  have eq1513995 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (τ (k X0 (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1513003 (M.op X0 x) (k X0 (k X0 (k X0 (σ (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)))))))
       have i₂ := eq231528 X0 X1 x
       grind)
    | exact superpose eq231528 eq1513003
    | exact resolve eq1513003 eq231528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231528 eq1513003
  have eq1531408 : ∀ X0 X1 : G, (τ (M.op (σ X1) X0)) = (τ (k (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1513995 (σ X1) (M.op X0 (σ X1))
       have i₂ := eq4645 X0 X1
       grind)
    | exact superpose eq4645 eq1513995
    | (have j1 := eq4645 X0 X1
       grind)
    | exact resolve eq1513995 eq4645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645 eq1513995
  have eq1532523 : ∀ X0 X1 : G, (τ (M.op (σ X1) X0)) = (τ (k (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1531408 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531408
  have eq1533053 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1532523 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1532523
    | (have j0 := eq1532523 X0 X1
       grind)
    | exact resolve eq1532523 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1532523
  have eq1533054 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1533053 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533053
  have eq1536352 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1533054 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1533054
    | exact resolve eq1533054 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533054
  have eq1538471 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1536352 X0 X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq1536352
    | (have j0 := eq1536352 X0 X1
       grind)
    | exact resolve eq1536352 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1536352
  have eq1540519 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq1538471 X0 X1
       grind)
    | exact superpose eq1538471 eq11
    | (have j1 := eq1538471 X0 X1
       grind)
    | exact resolve eq11 eq1538471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538471
  have eq1541178 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1540519 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq1540519
    | (have j0 := eq1540519 X0 X1
       grind)
    | exact resolve eq1540519 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540519
  have eq1544527 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1541178 (σ X0) (σ X1)
       grind)
    | exact superpose eq1541178 eq15
    | (have j1 := eq1541178 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq1541178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1544573 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1541178 (τ X0) X1
       grind)
    | exact superpose eq1541178 eq18
    | (have j1 := eq1541178 (τ X0) X1
       grind)
    | exact resolve eq18 eq1541178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1541178
  have eq1545032 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1544527 X0 X1
       have i₂ := eq4749 X1
       grind)
    | exact superpose eq4749 eq1544527
    | (have j0 := eq1544527 X0 X1
       grind)
    | exact resolve eq1544527 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4749 eq1544527
  have eq1545570 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1545032 X0 X1
       have i₂ := eq5088 X1
       grind)
    | exact superpose eq5088 eq1545032
    | (have j0 := eq1545032 X0 X1
       grind)
    | exact resolve eq1545032 eq5088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088 eq1545032
  have eq1555508 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1544573 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1544573
    | exact resolve eq1544573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544573
  have eq1557939 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1555508 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1555508
    | (have j0 := eq1555508 X0 X1
       grind)
    | exact resolve eq1555508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555508
  have eq1589841 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1545570 x y
       grind)
    | exact superpose eq1545570 eq16
    | (have j1 := eq1545570 x y
       grind)
    | exact resolve eq16 eq1545570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545570
  have eq1594712 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1589841
       have i₂ := eq1557939 x y
       grind)
    | exact superpose eq1557939 eq1589841
    | (have j1 := eq1557939 x y
       grind)
    | (have r₁ := eq1589841
       have r₂ := eq1557939 x y
       grind)
    | exact resolve eq1589841 eq1557939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557939 eq1589841
  have eq1594715 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1594712
  have eq1594746 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5922 y
       have i₂ := eq1594715
       grind)
    | exact superpose eq1594715 eq5922
    | exact resolve eq5922 eq1594715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594715
  have eq1595389 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1594746
       have r₂ := eq16
       grind)
    | exact resolve eq1594746 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594746
  have eq1599154 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1595389
       grind)
    | exact superpose eq1595389 eq10
    | exact resolve eq10 eq1595389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595389
  have eq1600300 : x = (M.op y y) := by
    first
    | (have i₁ := eq1599154
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1599154
    | exact resolve eq1599154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599154
  have eq1601149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5922 y
       have i₂ := eq1600300
       grind)
    | exact superpose eq1600300 eq5922
    | exact resolve eq5922 eq1600300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5922 eq1600300
  have eq1601894 : False := by grind
  exact eq1601894

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation1445 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1445 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  clear eq49
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq675 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq69
  have eq740 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq9569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9569
    | exact resolve eq9569 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9569
  have eq9581 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq9570
       have r₂ := eq28
       grind)
    | exact resolve eq9570 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9570
  have eq9585 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9581
    | exact resolve eq9581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9581
  have eq9597 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op (σ x) (σ y)) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9585 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9585
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9585
       grind)
    | exact resolve eq12 eq9585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9585
  have eq15205 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9597
    | (have j0 := eq9597 (σ x)
       grind)
    | (have r₁ := eq9597 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq9597 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9597
  have eq15206 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq15205
  have eq15207 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq15206
  have eq15215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq15207 eq77
    | exact resolve eq77 eq15207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq15207
  have eq15227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15215
  have eq15230 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15227
       have r₂ := eq28
       grind)
    | exact resolve eq15227 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15227
  have eq15234 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq15230
       grind)
    | exact superpose eq15230 eq96
    | exact resolve eq96 eq15230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15243 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq15230
       grind)
    | exact superpose eq15230 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15230
       grind)
    | exact resolve eq12 eq15230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15230
  have eq15279 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq15234
    | exact resolve eq15234 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15234
  have eq22373 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15243 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15243
    | (have j0 := eq15243 x
       grind)
    | (have r₁ := eq15243 x
       have r₂ := eq19
       grind)
    | exact resolve eq15243 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15243
  have eq22374 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq22373
  have eq22375 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq22374
  have eq22388 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq740 x y
       have i₂ := eq22375
       grind)
    | exact superpose eq22375 eq740
    | (have j0 := eq740 x y
       grind)
    | exact resolve eq740 eq22375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq22375
  have eq22392 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22388
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq22388
    | exact resolve eq22388 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22388
  have eq22404 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq22392
    | exact resolve eq22392 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22392
  have eq22409 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq22404
       have r₂ := eq15279
       grind)
    | exact resolve eq22404 eq15279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22404
  have eq22412 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22409
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq22409
    | exact resolve eq22409 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq22409
  have eq22415 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22412
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22412
    | exact resolve eq22412 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22412
  have eq22418 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22415
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22415
    | exact resolve eq22415 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22415
  have eq22421 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq22418
    | exact resolve eq22418 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22418
  have eq22424 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22421
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22421
    | exact resolve eq22421 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22421
  have eq22427 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22424
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22424
    | exact resolve eq22424 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22424
  have eq22428 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22427
  have eq22497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22428 eq15279
    | exact resolve eq15279 eq22428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15279 eq22428
  have eq22560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq22497
  have eq22568 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq22560
       have r₂ := eq28
       grind)
    | exact resolve eq22560 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22560
  have eq22571 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq22568 eq30
    | exact resolve eq30 eq22568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq22568
  have eq22690 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq22571
    | exact resolve eq22571 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22571
  have eq22691 : x = y := by grind
  clear eq22690
  have eq22712 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq22691
       grind)
    | exact superpose eq22691 eq19
    | exact resolve eq19 eq22691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq22713 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq22691
       grind)
    | exact superpose eq22691 eq25
    | exact resolve eq25 eq22691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22691
  have eq22837 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22713
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22713
    | exact resolve eq22713 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22713
  have eq22856 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22837 eq27
    | exact resolve eq27 eq22837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22837
  have eq23080 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq22856 eq68
    | exact resolve eq68 eq22856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq22856
  have eq23115 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq23080
       have i₂ := eq22712
       grind)
    | exact superpose eq22712 eq23080
    | exact resolve eq23080 eq22712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22712 eq23080
  have eq23131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23115 eq15
    | exact resolve eq15 eq23115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23115
  have eq23208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq23131
    | exact resolve eq23131 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23131
  have eq23229 : False := by grind
  exact eq23229

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation1445 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1445 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
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
  have eq153 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq155 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq3548 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq155 X1 X0
       grind)
    | exact superpose eq155 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq155 X1 X0
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq155 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq155 (M.op X1 (τ X1)) X1
       grind)
    | exact resolve eq13 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq3553 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3548 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3548
  have eq3554 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = (k (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3553 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq3627 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq4078 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3554 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3554
    | exact resolve eq3554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554
  have eq4139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4078 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4078
    | (have j0 := eq4078 X0 X1
       grind)
    | exact resolve eq4078 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4078
  have eq4185 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq4139 X1 X0
       grind)
    | exact superpose eq4139 eq10
    | (have j1 := eq4139 X1 X0
       grind)
    | exact resolve eq10 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4237 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4185 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq4185
    | (have j0 := eq4185 X0 X1
       grind)
    | exact resolve eq4185 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4185
  have eq4266 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq4237 (σ X0) X1
       grind)
    | exact superpose eq4237 eq28
    | (have j1 := eq4237 (σ X0) X1
       grind)
    | exact resolve eq28 eq4237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4237
  have eq4565 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq4266 X1 (σ X0)
       grind)
    | exact superpose eq4266 eq37
    | (have j1 := eq4266 X1 (σ X0)
       grind)
    | exact resolve eq37 eq4266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4266
  have eq4631 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4565 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4565
    | (have j0 := eq4565 X0 X1
       grind)
    | exact resolve eq4565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4565
  have eq4664 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4631 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4631
    | (have j0 := eq4631 X0 X1
       grind)
    | exact resolve eq4631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4631
  have eq4674 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4664 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4664
    | (have j0 := eq4664 X0 X1
       grind)
    | exact resolve eq4664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4664
  have eq4840 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4674 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq4674
    | (have j0 := eq4674 (τ X0) (τ X1)
       grind)
    | exact resolve eq4674 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4674
  have eq5041 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4840 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4840
    | (have j0 := eq4840 X0 X1
       grind)
    | exact resolve eq4840 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4840
  have eq5117 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5041 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5041
    | (have j0 := eq5041 X0 X1
       grind)
    | exact resolve eq5041 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5041
  have eq5177 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5117 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5117
    | (have j0 := eq5117 X0 X1
       grind)
    | exact resolve eq5117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5117
  have eq5235 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5177 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5177
    | (have j0 := eq5177 X0 X1
       grind)
    | exact resolve eq5177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5177
  have eq5324 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq5235 X1 X0
       grind)
    | exact superpose eq5235 eq11
    | (have j1 := eq5235 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq5235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5235
  have eq5449 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5324 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq5324
    | (have j0 := eq5324 X0 X1
       grind)
    | exact resolve eq5324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5324
  have eq5519 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5449 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5449
    | (have j0 := eq5449 (τ (σ X0)) (τ (σ (k X0 X1)))
       grind)
    | exact resolve eq5449 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5449
  have eq5692 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5519 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5519
    | (have j0 := eq5519 X0 X1
       grind)
    | exact resolve eq5519 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5519
  have eq5697 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5692 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5692
    | (have j0 := eq5692 X0 X1
       grind)
    | exact resolve eq5692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5692
  have eq6223 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5697 y x
       grind)
    | exact superpose eq5697 eq16
    | (have j1 := eq5697 x y
       grind)
    | exact resolve eq16 eq5697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5697
  have eq6262 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6223
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq6223
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq6223
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6223
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6223 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6263 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq6223
       have i₂ := eq4139 y x
       grind)
    | exact superpose eq4139 eq6223
    | (have j1 := eq4139 y x
       grind)
    | (have r₁ := eq6223
       have r₂ := eq4139 y x
       grind)
    | (have r₁ := eq6223
       have r₂ := eq4139 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6223
       have r₂ := eq4139 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6223 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139 eq6223
  have eq6266 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq6263
  have eq6267 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq6266
  have eq6268 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6262
  have eq6269 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6268
  have eq6272 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6267
       grind)
    | exact superpose eq6267 eq16
    | exact resolve eq16 eq6267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6267
  have eq6273 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6272
       have r₂ := eq22 x
       grind)
    | exact resolve eq6272 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6272
  have eq6279 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3627 x y
       have i₂ := eq6273
       grind)
    | exact superpose eq6273 eq3627
    | (have j0 := eq3627 x y
       grind)
    | exact resolve eq3627 eq6273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3627 eq6273
  have eq6284 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6279
  have eq6285 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6284
  have eq6299 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6285
       grind)
    | exact superpose eq6285 eq16
    | exact resolve eq16 eq6285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6285
  have eq6318 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6299
       have i₂ := eq6269
       grind)
    | exact superpose eq6269 eq6299
    | exact resolve eq6299 eq6269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6269 eq6299
  have eq6319 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6318
  have eq6320 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq6319
  have eq6321 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6320
       grind)
    | exact superpose eq6320 eq16
    | exact resolve eq16 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320
  have eq6322 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq6321
       have r₂ := eq22 x
       grind)
    | exact resolve eq6321 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6321
  have eq6323 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6322
       grind)
    | exact superpose eq6322 eq16
    | exact resolve eq16 eq6322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6324 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6322
       grind)
    | exact superpose eq6322 eq10
    | exact resolve eq10 eq6322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6322
  have eq6381 : x = y := by
    first
    | (have i₁ := eq6324
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6324
    | exact resolve eq6324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6324
  have eq6382 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6323
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6323
    | exact resolve eq6323 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6323
  have eq6383 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6382
       have i₂ := eq6381
       grind)
    | exact superpose eq6381 eq6382
    | exact resolve eq6382 eq6381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6381 eq6382
  have eq6384 : False := by grind
  exact eq6384

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation1445 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1445 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq153 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq155 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq867 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq155 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq155 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq155 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq13 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq872 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq867 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq873 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq872 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq2234 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq873 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq873
    | exact resolve eq873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq2277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2234 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2234
    | (have j0 := eq2234 X0 X1
       grind)
    | exact resolve eq2234 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2234
  have eq2312 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2277 X1 X0
       grind)
    | exact superpose eq2277 eq10
    | (have j1 := eq2277 X1 X0
       grind)
    | exact resolve eq10 eq2277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2354 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2312 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2312
    | (have j0 := eq2312 X0 X1
       grind)
    | exact resolve eq2312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312
  have eq2388 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq2354 X0 (σ X1)
       grind)
    | exact superpose eq2354 eq37
    | (have j1 := eq2354 X0 (σ X1)
       grind)
    | exact resolve eq37 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2354
  have eq3458 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq4294 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2388 (σ X0) X1
       grind)
    | exact superpose eq2388 eq28
    | (have j1 := eq2388 (σ X0) X1
       grind)
    | exact resolve eq28 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2388
  have eq4355 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4294 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4294
    | (have j0 := eq4294 X0 X1
       grind)
    | exact resolve eq4294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4294
  have eq4389 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4355 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4355
    | (have j0 := eq4355 X0 X1
       grind)
    | exact resolve eq4355 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4355
  have eq4399 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4389 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4389
    | (have j0 := eq4389 X0 X1
       grind)
    | exact resolve eq4389 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4389
  have eq4603 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4399 X1 X0
       grind)
    | exact superpose eq4399 eq11
    | (have j1 := eq4399 X1 X0
       grind)
    | exact resolve eq11 eq4399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4399
  have eq5485 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4603 y x
       grind)
    | exact superpose eq4603 eq16
    | (have j1 := eq4603 y x
       grind)
    | exact resolve eq16 eq4603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4603
  have eq5523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5485
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5485
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5485
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5485
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5485 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5485
       have i₂ := eq2277 y x
       grind)
    | exact superpose eq2277 eq5485
    | (have j1 := eq2277 y x
       grind)
    | (have r₁ := eq5485
       have r₂ := eq2277 y x
       grind)
    | (have r₁ := eq5485
       have r₂ := eq2277 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5485
       have r₂ := eq2277 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5485 eq2277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277 eq5485
  have eq5527 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5524
  have eq5528 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq5527
  have eq5529 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5523
  have eq5530 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5529
  have eq5534 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5528
       grind)
    | exact superpose eq5528 eq16
    | exact resolve eq16 eq5528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5528
  have eq5535 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5534
       have r₂ := eq22 x
       grind)
    | exact resolve eq5534 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5534
  have eq5541 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3458 x y
       have i₂ := eq5535
       grind)
    | exact superpose eq5535 eq3458
    | (have j0 := eq3458 x y
       grind)
    | exact resolve eq3458 eq5535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458 eq5535
  have eq5546 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5541
  have eq5547 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5546
  have eq5551 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5530
       grind)
    | exact superpose eq5530 eq16
    | exact resolve eq16 eq5530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5530
  have eq5552 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5551
       have r₂ := eq22 x
       grind)
    | exact resolve eq5551 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5551
  have eq5561 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5547
       grind)
    | exact superpose eq5547 eq16
    | exact resolve eq16 eq5547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5547
  have eq5583 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5561
       have i₂ := eq5552
       grind)
    | exact superpose eq5552 eq5561
    | exact resolve eq5561 eq5552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5552 eq5561
  have eq5584 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5583
  have eq5585 : (σ x) = (σ y) := by grind
  clear eq5584
  have eq5586 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5585
       grind)
    | exact superpose eq5585 eq16
    | exact resolve eq16 eq5585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5587 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5585
       grind)
    | exact superpose eq5585 eq10
    | exact resolve eq10 eq5585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5585
  have eq5643 : x = y := by
    first
    | (have i₁ := eq5587
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5587
    | exact resolve eq5587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5587
  have eq5644 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5586
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5586
    | exact resolve eq5586 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5586
  have eq5645 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5644
       have i₂ := eq5643
       grind)
    | exact superpose eq5643 eq5644
    | exact resolve eq5644 eq5643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5643 eq5644
  have eq5646 : False := by grind
  exact eq5646

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxy_pyy_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X2)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X0 (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq44
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq44 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq586 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 X1) X0 (M.op (M.op X0 (M.op X1 x)) x)
       have i₂ := eq52 X0 X1 x x
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq111 eq78
    | (have j0 := eq78 x (σ y)
       grind)
    | exact resolve eq78 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq842
    | exact resolve eq842 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq846 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq843
       have r₂ := eq27
       grind)
    | exact resolve eq843 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq851 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq846 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq846
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq846
       grind)
    | exact resolve eq13 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq859 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq851
  have eq889 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq859 eq88
    | exact resolve eq88 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq859
  have eq893 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq889
    | exact resolve eq889 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq889
  have eq908 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78 y y
       have i₂ := eq893
       grind)
    | exact superpose eq893 eq78
    | (have j0 := eq78 x y
       grind)
    | exact resolve eq78 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq909 : y = (M.op y y) := by grind
  clear eq908
  have eq915 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq909
       grind)
    | exact resolve eq13 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 : G, (M.op (M.op X0 y) (M.op X0 y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq14
    | exact resolve eq14 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq55 y y X0
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq55
    | exact resolve eq55 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : y = (k y y) := by grind
  clear eq915
  have eq931 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq925
       grind)
    | exact superpose eq925 eq76
    | exact resolve eq76 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq925
  have eq935 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq931
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq931
    | exact resolve eq931 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq931
  have eq950 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq935 eq78
    | (have j0 := eq78 x (σ y)
       grind)
    | exact resolve eq78 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq935
  have eq951 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq950
  have eq959 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq951 eq14
    | exact resolve eq14 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq951 eq55
    | exact resolve eq55 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1090 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq917 (M.op y (M.op y X0))
       have i₂ := eq920 X0
       grind)
    | exact superpose eq920 eq917
    | exact resolve eq917 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1104 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1090 X0
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq1090
    | exact resolve eq1090 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1299 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq962 eq959
    | exact resolve eq959 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1313 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq951 eq1299
    | exact resolve eq1299 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq1441 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq586 y X0
       have i₂ := eq1104 X0
       grind)
    | exact superpose eq1104 eq586
    | exact resolve eq586 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1443 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1313 eq586
    | exact resolve eq586 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq1313
  have eq1468 : ∀ X0 : G, (M.op y X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq917 (M.op y X0)
       have i₂ := eq1441 X0
       grind)
    | exact superpose eq1441 eq917
    | exact resolve eq917 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq1441
  have eq1482 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq1468 X0
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq1468
    | exact resolve eq1468 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq1468
  have eq1496 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1482 X0
       grind)
    | exact superpose eq1482 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1482 X0
       grind)
    | exact resolve eq13 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq1526 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1496 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1536 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1526 x
       grind)
    | exact superpose eq1526 eq44
    | exact resolve eq44 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1526
  have eq1547 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1536
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1536
    | exact resolve eq1536 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1536
  have eq1549 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1547
    | exact resolve eq1547 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1547
  have eq1566 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1443 eq959
    | exact resolve eq959 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959 eq1443
  have eq1580 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq951 eq1566
    | exact resolve eq1566 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq1566
  have eq1594 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1580 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1580 X0
       grind)
    | exact resolve eq13 eq1580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1580
  have eq1624 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1594 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1624 eq1549
    | exact resolve eq1549 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549 eq1624
  have eq1650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1639
    | exact resolve eq1639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1639
  have eq1658 : False := by grind
  exact eq1658
