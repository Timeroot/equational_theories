import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq59 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq59 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq249 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq256 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq249 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq249 X1 X1
       have r₂ := eq61 X1 X1
       grind)
    | exact resolve eq249 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq249
  have eq528 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq256 (σ X1) (σ X0)
       grind)
    | exact superpose eq256 eq15
    | exact resolve eq15 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 X1
       have i₂ := eq256 X1 X0
       grind)
    | exact superpose eq256 eq528
    | exact resolve eq528 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq528
  have eq538 : False := by grind
  exact eq538

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation1485 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (k (τ (σ X0)) X0) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq12 (τ (σ X0)) X0
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq12 X0 (τ (σ X0))
       have r₂ := eq10 X0
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq15
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq37
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq120 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq2214 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq120 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq2217 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2214 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq2214 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq2214 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq2214 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq2214 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq2241 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq2217 X0 (τ X1)
       grind)
    | exact superpose eq2217 eq29
    | (have j1 := eq2217 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq29 eq2217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq2242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2217 (σ X0) (σ X1)
       grind)
    | exact superpose eq2217 eq15
    | (have j1 := eq2217 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq2217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq8603 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2241 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2241
    | exact resolve eq2241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241
  have eq8650 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8603 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq8603
    | (have j0 := eq8603 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq8603 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8603
  have eq19333 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2242 x y
       grind)
    | exact superpose eq2242 eq16
    | (have j1 := eq2242 x y
       grind)
    | exact resolve eq16 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq19883 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19333
       have i₂ := eq8650 y x
       grind)
    | exact superpose eq8650 eq19333
    | (have j1 := eq8650 (σ x) (σ y)
       grind)
    | (have r₁ := eq19333
       have r₂ := eq8650 y x
       grind)
    | (have r₁ := eq19333
       have r₂ := eq8650 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq19333
       have r₂ := eq8650 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq19333 eq8650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8650 eq19333
  have eq19884 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq19883
  have eq20383 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19884
       grind)
    | exact superpose eq19884 eq10
    | exact resolve eq10 eq19884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19884
  have eq20439 : x = y ∨ x = y := by
    first
    | (have i₁ := eq20383
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20383
    | exact resolve eq20383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20383
  have eq20440 : x = y := by grind
  clear eq20439
  have eq20710 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20440
       grind)
    | exact superpose eq20440 eq16
    | exact resolve eq16 eq20440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20440
  have eq20711 : False := by grind
  exact eq20711

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1485 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  clear eq19
  have eq99 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq29
    | (have j0 := eq29 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40
    | exact resolve eq40 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq688 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq671
    | (have j0 := eq671 X0 X1
       grind)
    | exact resolve eq671 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq1586 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq99 x y
       grind)
    | exact superpose eq99 eq16
    | (have j1 := eq99 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq99 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq99 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq99 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1586
  have eq2164 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1629
       grind)
    | exact superpose eq1629 eq16
    | exact resolve eq16 eq1629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2173 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1629
       grind)
    | exact superpose eq1629 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1629
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1629
       grind)
    | exact resolve eq13 eq1629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629
  have eq2202 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2173
  have eq2203 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2202
  have eq2205 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2203
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2203
    | exact resolve eq2203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203
  have eq6601 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq688 y x
       have i₂ := eq2205
       grind)
    | exact superpose eq2205 eq688
    | (have j0 := eq688 y x
       grind)
    | exact resolve eq688 eq2205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq6603 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq2205
       grind)
    | exact superpose eq2205 eq10
    | exact resolve eq10 eq2205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq6638 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6601
  have eq6647 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6603
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6603
    | exact resolve eq6603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6603
  have eq6648 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6638
       have r₂ := eq2164
       grind)
    | exact resolve eq6638 eq2164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164 eq6638
  have eq6651 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq6647
       have r₂ := eq13 x y
       grind)
    | exact resolve eq6647 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6647
  have eq12786 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29 x y
       have i₂ := eq6651
       grind)
    | exact superpose eq6651 eq29
    | (have j0 := eq29 x y
       grind)
    | exact resolve eq29 eq6651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6651
  have eq12789 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12786
  have eq18498 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq12789
       grind)
    | exact superpose eq12789 eq16
    | exact resolve eq16 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12789
  have eq22463 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18498
       have i₂ := eq6648
       grind)
    | exact superpose eq6648 eq18498
    | exact resolve eq18498 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6648 eq18498
  have eq22464 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22463
  have eq22465 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq22464
  have eq27298 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22465
       grind)
    | exact superpose eq22465 eq10
    | exact resolve eq10 eq22465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22465
  have eq27365 : x = y ∨ x = y := by
    first
    | (have i₁ := eq27298
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27298
    | exact resolve eq27298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27298
  have eq27366 : x = y := by grind
  clear eq27365
  have eq34320 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27366
       grind)
    | exact superpose eq27366 eq16
    | exact resolve eq16 eq27366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27366
  have eq34321 : False := by grind
  exact eq34321

/-- `Equation1487`: `x = (y ◇ x) ◇ (x ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then Y else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_y_x_Equation1487 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) Law1487 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1487.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq30 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 X0 (M.op x y)
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15
    | (have j0 := eq15 y X0
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
  have eq43 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
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
  have eq60 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq31
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
  have eq96 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq79 eq56
    | exact resolve eq56 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq101 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 X0) (M.op X1 X2)
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq12
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq105 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0 X0
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
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
  have eq136 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 (σ y) (σ (k y x))
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq140 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq136
    | exact resolve eq136 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
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
  have eq232 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 (M.op X0 X0)
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq29
    | exact resolve eq29 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq237 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq37
    | exact resolve eq37 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq275 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq1369 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq232 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq232
    | (have j0 := eq232 x
       grind)
    | exact resolve eq232 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq1400 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1369 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq14 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1401 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1400
       have i₂ := eq56 sF2 sF2 sF2
       grind)
    | exact superpose eq56 eq1400
    | exact resolve eq1400 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq2065 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq237
    | (have j0 := eq237 (M.op x y)
       grind)
    | exact resolve eq237 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq2445 : (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2065 eq14
    | (have j0 := eq14 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2446 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2445
       have i₂ := eq56 sF1 sF1 sF1
       grind)
    | exact superpose eq56 eq2445
    | exact resolve eq2445 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2445
  have eq5129 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X0 X1
       have i₂ := eq56 X0 X0 X0
       grind)
    | exact superpose eq56 eq101
    | (have j0 := eq101 X0 X0 X1
       grind)
    | (have r₁ := eq101 X0 X0 x
       have r₂ := eq56 X0 X0 X0
       grind)
    | exact resolve eq101 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq5130 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5129 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5129
  have eq5134 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq96 eq105
    | (have r₁ := eq105 (M.op x y) y
       have r₂ := eq96 (M.op x y)
       grind)
    | exact resolve eq105 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5135 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq92 eq105
    | (have r₁ := eq105 x (M.op x y)
       have r₂ := eq92 x
       grind)
    | exact resolve eq105 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq5141 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5135
  have eq5142 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5134
  have eq5146 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5141 eq1401
    | exact resolve eq1401 eq5141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401 eq5141
  have eq5149 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5142 eq2446
    | exact resolve eq2446 eq5142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446
  have eq5150 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5142 eq2065
    | exact resolve eq2065 eq5142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065 eq5142
  have eq5152 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5146
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5146
    | exact resolve eq5146 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5146
  have eq5154 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq5150
    | exact resolve eq5150 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5150
  have eq5155 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq5149
    | exact resolve eq5149 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq11899 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq5152 eq56
    | exact resolve eq56 eq5152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5152
  have eq11912 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5155 eq56
    | exact resolve eq56 eq5155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq13025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11912 eq11899
    | exact resolve eq11899 eq11912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11912
  have eq13040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq13025
    | exact resolve eq13025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13025
  have eq13042 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq13040
       have r₂ := eq28
       grind)
    | exact resolve eq13040 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13040
  have eq13075 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13042 eq5130
    | exact resolve eq5130 eq13042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13042
  have eq13081 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq13075
       have i₂ := eq106 sF1
       grind)
    | exact superpose eq106 eq13075
    | exact resolve eq13075 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13075
  have eq13148 : (τ (σ y)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13081 eq275
    | exact resolve eq275 eq13081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq13164 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq13081
  have eq13173 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq38 eq13148
    | exact resolve eq13148 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13148
  have eq13188 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq40 eq13173
    | exact resolve eq13173 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13173
  have eq13311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13188 eq5155
    | exact resolve eq5155 eq13188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5155 eq13188
  have eq13341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13311
  have eq13354 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq13341
    | exact resolve eq13341 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13341
  have eq13365 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13354
       have r₂ := eq28
       grind)
    | exact resolve eq13354 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13354
  have eq13374 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13365 eq144
    | exact resolve eq144 eq13365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13365
  have eq13399 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq13374
    | exact resolve eq13374 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13374
  have eq13402 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13399
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13399
    | exact resolve eq13399 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13399
  have eq13448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13402 eq11899
    | exact resolve eq11899 eq13402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13448
  have eq13486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq13472
    | exact resolve eq13472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13472
  have eq13498 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13486
       have r₂ := eq28
       grind)
    | exact resolve eq13486 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13486
  have eq13586 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13498 eq5130
    | exact resolve eq5130 eq13498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13498
  have eq13592 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13586
       have i₂ := eq106 sF1
       grind)
    | exact superpose eq106 eq13586
    | exact resolve eq13586 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13586
  have eq13609 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13592
       have r₂ := eq13164
       grind)
    | exact resolve eq13592 eq13164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13164 eq13592
  have eq15078 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13609 eq13402
    | exact resolve eq13402 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13402
  have eq15079 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13609 eq11899
    | exact resolve eq11899 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13609
  have eq15103 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15079
  have eq15104 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15078
  have eq15130 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15104 eq27
    | exact resolve eq27 eq15104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15134 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15104 eq40
    | exact resolve eq40 eq15104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15104
  have eq15190 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq39 eq15134
    | exact resolve eq15134 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15134
  have eq15199 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq15190 eq40
    | exact resolve eq40 eq15190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15190
  have eq15246 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq15199
    | exact resolve eq15199 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15199
  have eq15254 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15246 eq39
    | exact resolve eq39 eq15246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15246
  have eq15302 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq15254
    | exact resolve eq15254 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15254
  have eq15507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15130 eq15103
    | exact resolve eq15103 eq15130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15103 eq15130
  have eq15534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15507
  have eq15551 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq15534
       have r₂ := eq28
       grind)
    | exact resolve eq15534 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15534
  have eq15562 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15551 eq40
    | exact resolve eq40 eq15551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15551
  have eq15609 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq15562
    | exact resolve eq15562 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15562
  have eq15617 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15609 eq39
    | exact resolve eq39 eq15609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15609
  have eq15665 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq15617
    | exact resolve eq15617 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15617
  have eq15669 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15665 eq21
    | exact resolve eq21 eq15665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15671 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15665 eq96
    | exact resolve eq96 eq15665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq15696 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq15665
  have eq15697 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15669
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15669
    | exact resolve eq15669 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15669
  have eq16314 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15671 (M.op x y)
       have i₂ := eq15671 x
       grind)
    | exact superpose eq15671 eq15671
    | exact resolve eq15671 eq15671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15671
  have eq16330 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq16314
  have eq16355 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq144 y
       have i₂ := eq16330
       grind)
    | exact superpose eq16330 eq144
    | exact resolve eq144 eq16330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16330
  have eq16380 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16355
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16355
    | exact resolve eq16355 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16355
  have eq16383 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15697 eq16380
    | exact resolve eq16380 eq15697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15697 eq16380
  have eq16431 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq16383
  have eq17381 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16431 eq5154
    | exact resolve eq5154 eq16431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154
  have eq17440 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43 eq17381
    | exact resolve eq17381 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq17381
  have eq17575 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15302 eq17440
    | exact resolve eq17440 eq15302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15302 eq17440
  have eq17623 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq17575
  have eq17656 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17623
       have r₂ := eq15696
       grind)
    | exact resolve eq17623 eq15696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15696 eq17623
  have eq17659 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17656
       have i₂ := eq106 y
       grind)
    | exact superpose eq106 eq17656
    | exact resolve eq17656 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17656
  have eq17661 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17659
       have i₂ := eq144 y
       grind)
    | exact superpose eq144 eq17659
    | exact resolve eq17659 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17659
  have eq17663 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17661
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17661
    | exact resolve eq17661 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17661
  have eq17702 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17663 eq5130
    | exact resolve eq5130 eq17663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17663
  have eq17712 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17702
       have i₂ := eq106 sF1
       grind)
    | exact superpose eq106 eq17702
    | exact resolve eq17702 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17702
  have eq17765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17712 eq11899
    | exact resolve eq11899 eq17712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11899 eq17712
  have eq17802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17765
    | exact resolve eq17765 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17765
  have eq17814 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17802
       have r₂ := eq28
       grind)
    | exact resolve eq17802 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq35408 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17814 eq5130
    | exact resolve eq5130 eq17814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5130 eq17814
  have eq35416 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35408
       have i₂ := eq106 sF1
       grind)
    | exact superpose eq106 eq35408
    | exact resolve eq35408 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq35408
  have eq37421 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35416 eq16431
    | exact resolve eq16431 eq35416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16431 eq35416
  have eq37484 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq37421
  have eq37515 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37484 eq39
    | exact resolve eq39 eq37484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq37484
  have eq37569 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq37515
    | exact resolve eq37515 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq37515
  have eq37570 : x = (M.op x y) := by grind
  clear eq37569
  have eq37575 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37570 eq21
    | exact resolve eq21 eq37570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq37583 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq37570 eq92
    | exact resolve eq92 eq37570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq37586 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq37570 eq102
    | exact resolve eq102 eq37570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq41378 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq37570 eq37586
    | exact resolve eq37586 eq37570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37570 eq37586
  have eq41381 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37575
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37575
    | exact resolve eq37575 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37575
  have eq41777 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq41381 eq23
    | exact resolve eq23 eq41381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq41778 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq41381 eq27
    | exact resolve eq27 eq41381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41789 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41381 eq140
    | exact resolve eq140 eq41381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq43785 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | exact superpose eq41381 eq41789
    | exact resolve eq41789 eq41381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41381 eq41789
  have eq44322 : x = (M.op x x) := by
    first
    | (have i₁ := eq37583 (M.op x x)
       have i₂ := eq37583 x
       grind)
    | exact superpose eq37583 eq37583
    | exact resolve eq37583 eq37583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37583
  have eq44472 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq41378
       have i₂ := eq44322
       grind)
    | exact superpose eq44322 eq41378
    | (have r₁ := eq41378
       have r₂ := eq44322
       grind)
    | exact resolve eq41378 eq44322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41378
  have eq44495 : x = (k y x) := by grind
  clear eq44472
  have eq44539 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43785
       have i₂ := eq44495
       grind)
    | exact superpose eq44495 eq43785
    | exact resolve eq43785 eq44495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43785 eq44495
  have eq44564 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq44539
       have i₂ := eq41777
       grind)
    | exact superpose eq41777 eq44539
    | exact resolve eq44539 eq41777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44539
  have eq44565 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq44564
  have eq44746 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq144 x
       have i₂ := eq44322
       grind)
    | exact superpose eq44322 eq144
    | exact resolve eq144 eq44322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq44322
  have eq44797 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq44746
       have i₂ := eq41777
       grind)
    | exact superpose eq41777 eq44746
    | exact resolve eq44746 eq41777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41777 eq44746
  have eq44973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq44797 eq44565
    | exact resolve eq44565 eq44797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44565
  have eq44987 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq44973
       have r₂ := eq28
       grind)
    | exact resolve eq44973 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44973
  have eq46071 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq44987 eq41778
    | exact resolve eq41778 eq44987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41778 eq44987
  have eq46107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44797 eq46071
    | exact resolve eq46071 eq44797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44797 eq46071
  have eq46591 : False := by grind
  exact eq46591

/-- `Equation1496`: `x = (y ◇ x) ◇ (y ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_x_pxx_pxy_Equation1496 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1496 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1496.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
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
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
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
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
       have i₂ := eq16 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq34
    | exact resolve eq34 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq337 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq337
    | exact resolve eq337 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq407 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq561 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq407 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq407
    | exact resolve eq407 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq407
  have eq590 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq561 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq561
    | exact resolve eq561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq702 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 (M.op X1 X1) (M.op X1 X1)
       have i₂ := eq179 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq702 X1 X0
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq13
    | (have j0 := eq13 X0 X2
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq702 X0 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X0 X0)
       have r₂ := eq702 X0 X1
       grind)
    | exact resolve eq13 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X1
       have i₂ := eq702 (σ X1) X0
       grind)
    | (have i₁ := eq590 X1
       have i₂ := eq702 X0 (σ X1)
       grind)
    | exact superpose eq702 eq590
    | exact resolve eq590 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq742 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365 X1
       have i₂ := eq702 (τ X1) X0
       grind)
    | (have i₁ := eq365 X1
       have i₂ := eq702 X0 (τ X1)
       grind)
    | exact superpose eq702 eq365
    | exact resolve eq365 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq775 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ (M.op X1 X1))
       have i₂ := eq742 X1 (τ X0)
       grind)
    | exact superpose eq742 eq34
    | exact resolve eq34 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq794 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq775
    | exact resolve eq775 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq830 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op x x) := by
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
  have eq833 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq837 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1544 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq837 X0
       have i₂ := eq702 X0 X1
       grind)
    | (have i₁ := eq837 X1
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq837
    | exact resolve eq837 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq1645 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq830
       grind)
    | exact superpose eq830 eq40
    | exact resolve eq40 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq830
  have eq1646 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1645
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1645
    | exact resolve eq1645 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1648 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1646
    | exact resolve eq1646 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq2315 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X1 (σ (M.op X1 X1))
       have i₂ := eq1544 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq1544 eq742
    | (have j1 := eq1544 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq742 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2317 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq794 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq1544 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq1544 eq794
    | (have j1 := eq1544 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact resolve eq794 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq2321 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X1 (τ (M.op X1 X1))
       have i₂ := eq1544 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1544 eq741
    | (have j1 := eq1544 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq741 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2329 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1544 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq2333 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2321 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq2336 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317
  have eq2338 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2315 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2315
  have eq2389 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 x
       have i₂ := eq2338 x X0
       grind)
    | exact superpose eq2338 eq16
    | exact resolve eq16 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2393 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X2) X3) X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq179 X2 x X3
       have i₂ := eq2338 x X0
       grind)
    | exact superpose eq2338 eq179
    | exact resolve eq179 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2460 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 (M.op X1 X1) X1 X2
       have i₂ := eq2338 (M.op X1 X1) X0
       grind)
    | exact superpose eq2338 eq179
    | exact resolve eq179 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2570 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 x
       have i₂ := eq2333 x X0
       grind)
    | exact superpose eq2333 eq16
    | exact resolve eq16 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2572 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq175 x
       have i₂ := eq2333 x X0
       grind)
    | exact superpose eq2333 eq175
    | exact resolve eq175 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2333
  have eq2803 : ∀ X0 X2 : G, (σ (M.op X2 X2)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq2338 x X2
       have i₂ := eq2336 x X0
       grind)
    | exact superpose eq2336 eq2338
    | exact resolve eq2338 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336
  have eq16483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq1648 eq833
    | exact resolve eq833 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq1648
  have eq16492 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16483
       have r₂ := eq27
       grind)
    | exact resolve eq16483 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16483
  have eq16527 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq16492 eq741
    | exact resolve eq741 eq16492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq16492
  have eq16765 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq31 eq16527
    | exact resolve eq16527 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16527
  have eq16839 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16765 X0
       have j1 := eq730 X0 X0 y
       grind)
    | (have r₁ := eq16765 (M.op X0 X0)
       have r₂ := eq730 X0 x (k (M.op X0 X0) y)
       grind)
    | (have r₁ := eq16765 X0
       have r₂ := eq730 x x y
       grind)
    | exact resolve eq16765 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq16765
  have eq16985 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2329 X0 y
       have i₂ := eq16839 y
       grind)
    | exact superpose eq16839 eq2329
    | (have j0 := eq2329 X0 y
       grind)
    | (have r₁ := eq2329 X0 y
       have r₂ := eq16839 y
       grind)
    | exact resolve eq2329 eq16839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329 eq16839
  have eq17002 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16985 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16985
  have eq17242 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2803 x X0
       have i₂ := eq17002 x
       grind)
    | exact superpose eq17002 eq2803
    | exact resolve eq2803 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2803
  have eq17273 : ∀ X0 X1 : G, (M.op y (M.op X0 (σ (M.op X1 X1)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2389 X1 X0 X0
       have i₂ := eq17002 X0
       grind)
    | exact superpose eq17002 eq2389
    | exact resolve eq2389 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq17276 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X1 X1))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq17002 X0
       grind)
    | exact superpose eq17002 eq16
    | exact resolve eq16 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17315 : ∀ X0 : G, y = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2460 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq17002 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq17002 eq2460
    | exact resolve eq2460 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460
  have eq17324 : ∀ X0 X1 : G, (M.op (M.op y X1) (σ (M.op X0 X0))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2393 X0 (σ (M.op X0 X0)) X1
       have i₂ := eq17002 (σ (M.op X0 X0))
       grind)
    | exact superpose eq17002 eq2393
    | exact resolve eq2393 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393
  have eq17347 : ∀ X1 : G, (M.op (M.op y X1) (σ y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq17002 eq17324
    | exact resolve eq17324 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17324
  have eq17352 : y = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17002 eq17315
    | exact resolve eq17315 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17315
  have eq17383 : ∀ X0 : G, (M.op y (M.op X0 y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17002 eq17276
    | exact resolve eq17276 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17276
  have eq17387 : ∀ X0 : G, (M.op y (M.op X0 (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17002 eq17273
    | exact resolve eq17273 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17273
  have eq17406 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17242 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17242
    | (have j0 := eq17242 X0
       grind)
    | exact resolve eq17242 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17242
  have eq17553 : ∀ X1 : G, (M.op (M.op y X1) (σ y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq17347 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17347
    | (have j0 := eq17347 X1
       grind)
    | exact resolve eq17347 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17347
  have eq17556 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17352
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17352
    | exact resolve eq17352 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17352
  have eq17575 : ∀ X0 : G, (M.op y (M.op X0 (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17387 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17387
    | (have j0 := eq17387 X0
       grind)
    | exact resolve eq17387 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17387
  have eq17593 : (σ y) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17002 eq17406
    | exact resolve eq17406 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17406
  have eq17691 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17556 eq17575
    | exact resolve eq17575 eq17556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17575
  have eq17704 : (σ y) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17593
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17593
    | exact resolve eq17593 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17593
  have eq17806 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq17556 eq31
    | exact resolve eq31 eq17556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17840 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq17806
    | exact resolve eq17806 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17806
  have eq17841 : y = (σ y) ∨ x = y := by grind
  clear eq17840
  have eq17842 : (M.op x y) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq17841
       grind)
    | exact superpose eq17841 eq18
    | exact resolve eq18 eq17841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17864 : x ≠ (σ y) ∨ x = y := by grind
  have eq20140 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17383 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17383
    | (have j0 := eq17383 x
       grind)
    | exact resolve eq17383 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17383
  have eq20173 : x = (M.op (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17556 eq20140
    | exact resolve eq20140 eq17556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20140
  have eq20361 : ∀ X0 : G, (M.op (k y X0) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq17553 X0
       have i₂ := eq11 y X0
       grind)
    | exact superpose eq11 eq17553
    | (have j1 := eq11 y X0
       grind)
    | exact resolve eq17553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17553
  have eq20408 : ∀ X0 : G, (M.op (k y X0) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq17002 eq20361
    | (have j0 := eq20361 X0
       grind)
    | exact resolve eq20361 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20361
  have eq20409 : ∀ X0 : G, (M.op (k y X0) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq20408 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20408
  have eq20436 : ∀ X0 : G, (M.op (k (σ y) X0) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq17556 eq20409
    | (have j0 := eq20409 x
       grind)
    | exact resolve eq20409 eq17556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20409
  have eq20455 : ∀ X0 : G, (M.op (k (σ y) X0) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = X0 := by
    intro X0
    first
    | exact superpose eq17556 eq20436
    | (have j0 := eq20436 X0
       grind)
    | exact resolve eq20436 eq17556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20436
  have eq42368 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = X0 := by
    intro X0
    first
    | exact superpose eq20455 eq17691
    | (have j1 := eq20455 (σ x)
       grind)
    | exact resolve eq17691 eq20455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17691
  have eq42381 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = X0 := by
    intro X0
    first
    | (have j0 := eq42368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42368
  have eq43753 : x = (k (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq42381 eq20173
    | (have j1 := eq42381 (σ x)
       grind)
    | exact resolve eq20173 eq42381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42381
  have eq43800 : x = (k (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq43753
  have eq43986 : (σ x) = (k (σ (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq43800 eq41
    | exact resolve eq41 eq43800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq43800
  have eq43992 : (σ x) = (k (σ (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq43986
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43986
    | exact resolve eq43986 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43986
  have eq43996 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq17704 eq43992
    | exact resolve eq43992 eq17704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17704 eq43992
  have eq44002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq43996 eq20455
    | (have j0 := eq20455 (σ x)
       grind)
    | exact resolve eq20455 eq43996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20455 eq43996
  have eq44008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by grind
  clear eq44002
  have eq44012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26 eq44008
    | exact resolve eq44008 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44008
  have eq44017 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq44012
       have r₂ := eq27
       grind)
    | exact resolve eq44012 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44012
  have eq44366 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq44017 eq31
    | exact resolve eq31 eq44017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44017
  have eq44443 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq44366
    | exact resolve eq44366 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44366
  have eq44444 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq44443
  have eq44461 : (M.op x y) = (τ (σ y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq44444 eq28
    | exact resolve eq28 eq44444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq44444
  have eq44507 : (M.op x y) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq44461
    | exact resolve eq44461 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44461
  have eq44524 : y = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq44507 eq31
    | exact resolve eq31 eq44507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44572 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq44507 eq17556
    | exact resolve eq17556 eq44507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17556 eq44507
  have eq44641 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq44572
  have eq44716 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq17841 eq44524
    | exact resolve eq44524 eq17841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44524
  have eq44740 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq17841 eq44716
    | exact resolve eq44716 eq17841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44716
  have eq44774 : x = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq44641 eq29
    | exact resolve eq29 eq44641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44641
  have eq44903 : x = (τ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17841 eq44774
    | exact resolve eq44774 eq17841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44774
  have eq44941 : x = (σ y) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq44740 eq44903
    | exact resolve eq44903 eq44740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44740 eq44903
  have eq44958 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq44941
       have r₂ := eq17864
       grind)
    | exact resolve eq44941 eq17864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17864 eq44941
  have eq44970 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq44958 eq31
    | exact resolve eq31 eq44958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq45023 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq44958 eq17842
    | exact resolve eq17842 eq44958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17842
  have eq45031 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq44958 eq20173
    | exact resolve eq20173 eq44958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20173
  have eq45074 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq45031
  have eq45082 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq45023
  have eq45146 : (σ y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq17841 eq44970
    | exact resolve eq44970 eq17841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17841 eq44970
  have eq45174 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq44958 eq45146
    | exact resolve eq45146 eq44958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45146
  have eq45301 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x (τ (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq45082 eq2570
    | exact resolve eq2570 eq45082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570 eq45082
  have eq45313 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2572 eq45301
    | exact resolve eq45301 eq2572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572 eq45301
  have eq45395 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq45313
  have eq46140 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq45074 eq17002
    | exact resolve eq17002 eq45074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17002 eq45074
  have eq46170 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by grind
  clear eq46140
  have eq46193 : x = y ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq44958 eq46170
    | exact resolve eq46170 eq44958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44958 eq46170
  have eq46194 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq46193
  have eq46323 : x = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq46194 eq29
    | exact resolve eq29 eq46194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq46194
  have eq46455 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq45174 eq46323
    | exact resolve eq46323 eq45174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45174 eq46323
  have eq46475 : x = y := by
    first
    | (have r₁ := eq46455
       have r₂ := eq45395
       grind)
    | exact resolve eq46455 eq45395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45395 eq46455
  have eq46490 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq46475
       grind)
    | exact superpose eq46475 eq18
    | exact resolve eq18 eq46475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq46491 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq46475
       grind)
    | exact superpose eq46475 eq24
    | exact resolve eq24 eq46475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq46475
  have eq46509 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq46491
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46491
    | exact resolve eq46491 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq46491
  have eq46513 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq46509 eq26
    | exact resolve eq26 eq46509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq46509
  have eq46616 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq702 X0 x
       have i₂ := eq46490
       grind)
    | exact superpose eq46490 eq702
    | exact resolve eq702 eq46490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46679 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2338 X0 x
       have i₂ := eq46490
       grind)
    | exact superpose eq46490 eq2338
    | exact resolve eq2338 eq46490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq46490
  have eq46836 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq46679
    | (have j0 := eq46679 X0
       grind)
    | exact resolve eq46679 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq46679
  have eq46923 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq46836 x
       have i₂ := eq46616 x
       grind)
    | exact superpose eq46616 eq46836
    | exact resolve eq46836 eq46616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46836
  have eq47197 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq46513 eq702
    | exact resolve eq702 eq46513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq46513
  have eq47464 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47197 x
       have i₂ := eq46616 x
       grind)
    | exact superpose eq46616 eq47197
    | exact resolve eq47197 eq46616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46616 eq47197
  have eq47752 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq47464 eq27
    | exact resolve eq27 eq47464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq47464
  have eq47786 : False := by grind
  exact eq47786

/-- `Equation1496`: `x = (y ◇ x) ◇ (y ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_x_pxx_pyx_Equation1496 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1496 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1496.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq44
    | (have j0 := eq44 (M.op x y)
       grind)
    | exact resolve eq44 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq131 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
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
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X1 (M.op X2 X2)) (M.op X1 X0) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
       have i₂ := eq16 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 X1))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq34
    | exact resolve eq34 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq337 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq337
    | exact resolve eq337 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq407 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq561 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq407 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq407
    | exact resolve eq407 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq590 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq561 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq561
    | exact resolve eq561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq701 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 (M.op X1 X1) (M.op X1 X1)
       have i₂ := eq179 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq702 X1 X0
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq13
    | (have j0 := eq13 X0 X2
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq702 X0 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X0 X0)
       have r₂ := eq702 X0 X1
       grind)
    | exact resolve eq13 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq702 X1 X0
       grind)
    | (have i₁ := eq174 X1
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq174
    | exact resolve eq174 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq739 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 (M.op X1 X1) X1 X2
       have i₂ := eq702 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq179 (M.op X1 X1) X1 X2
       have i₂ := eq702 X0 (M.op X1 X1)
       grind)
    | exact superpose eq702 eq179
    | exact resolve eq179 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X1
       have i₂ := eq702 (σ X1) X0
       grind)
    | (have i₁ := eq590 X1
       have i₂ := eq702 X0 (σ X1)
       grind)
    | exact superpose eq702 eq590
    | exact resolve eq590 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq742 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365 X1
       have i₂ := eq702 (τ X1) X0
       grind)
    | (have i₁ := eq365 X1
       have i₂ := eq702 X0 (τ X1)
       grind)
    | exact superpose eq702 eq365
    | exact resolve eq365 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ (M.op X1 X1))
       have i₂ := eq742 X1 (τ X0)
       grind)
    | exact superpose eq742 eq34
    | exact resolve eq34 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq775
    | exact resolve eq775 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq825 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (k (M.op X0 X0) X1)) = X2 ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq11 (M.op X0 X0) X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op X0 X0) X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq794 (τ X0) X1
       grind)
    | exact superpose eq794 eq34
    | exact resolve eq34 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq794
  have eq953 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq934 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq934
    | exact resolve eq934 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1178 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op (M.op X0 X0) (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq365 X2
       have i₂ := eq701 (τ X2) X0 X1
       grind)
    | exact superpose eq701 eq365
    | exact resolve eq365 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq701
  have eq1550 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0
       have i₂ := eq702 X0 X1
       grind)
    | (have i₁ := eq843 X1
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq843
    | exact resolve eq843 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1567 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq702 X1 X0
       have i₂ := eq843 X0
       grind)
    | exact superpose eq843 eq702
    | (have j1 := eq843 X0
       grind)
    | exact resolve eq702 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1623 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1651 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq830
       grind)
    | exact superpose eq830 eq39
    | exact resolve eq39 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq1652 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1651
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1651
    | exact resolve eq1651 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq1654 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1652
    | exact resolve eq1652 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq2239 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq702 X1 X2
       have i₂ := eq1550 X2 X0
       grind)
    | exact superpose eq1550 eq702
    | (have j1 := eq1550 X1 X0
       grind)
    | exact resolve eq702 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2241 : ∀ X0 X1 X2 : G, (k X1 (k X0 X0)) = X1 ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq732 X2 X1
       have i₂ := eq1550 X2 X0
       grind)
    | exact superpose eq1550 eq732
    | (have j1 := eq1550 X2 X0
       grind)
    | exact resolve eq732 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2321 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X1 (σ (M.op X1 X1))
       have i₂ := eq1550 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq1550 eq742
    | (have j1 := eq1550 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq742 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2322 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) ∨ (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1178 X1 X2 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       have i₂ := eq1550 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact superpose eq1550 eq1178
    | (have j1 := eq1550 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact resolve eq1178 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq2324 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) ∨ (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq953 (σ (σ (σ (M.op X1 X1)))) X1
       have i₂ := eq1550 X0 (σ (σ (σ (M.op X1 X1))))
       grind)
    | exact superpose eq1550 eq953
    | (have j1 := eq1550 X0 (σ (σ (σ (M.op X1 X1))))
       grind)
    | exact resolve eq953 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq2327 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X1 (τ (M.op X1 X1))
       have i₂ := eq1550 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1550 eq741
    | (have j1 := eq1550 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq741 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2335 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1550 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq2339 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2327 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327
  have eq2341 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq2324 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2324
  have eq2343 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2322 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2322
  have eq2344 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2321 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq2399 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X2) X3) X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq179 X2 x X3
       have i₂ := eq2344 x X0
       grind)
    | exact superpose eq2344 eq179
    | exact resolve eq179 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2466 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 (M.op X1 X1) X1 X2
       have i₂ := eq2344 (M.op X1 X1) X0
       grind)
    | exact superpose eq2344 eq179
    | exact resolve eq179 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2648 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (τ (M.op X0 X0)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq739 X1 X2 (M.op X1 X1)
       have i₂ := eq2339 (M.op X1 X1) X0
       grind)
    | exact superpose eq2339 eq739
    | exact resolve eq739 eq2339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq2339
  have eq4091 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op X0 (M.op (M.op x X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 x
       have i₂ := eq177 X0 x x X1
       grind)
    | (have i₁ := eq175 (M.op x x)
       have i₂ := eq177 x x x x
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4092 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op (σ x) X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x
       have i₂ := eq177 X0 sF2 x x
       grind)
    | (have i₁ := eq176 (M.op sF2 sF2)
       have i₂ := eq177 sF2 sF2 x sF2
       grind)
    | exact superpose eq177 eq176
    | exact resolve eq176 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq177
  have eq7695 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1623 X1
       have i₂ := eq1567 X1 X0
       grind)
    | exact superpose eq1567 eq1623
    | (have j0 := eq1623 X1
       have j1 := eq1567 X1 X1
       grind)
    | (have r₁ := eq1623 (M.op X1 X1)
       have r₂ := eq1567 (M.op X1 X1) X1
       grind)
    | exact resolve eq1623 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567 eq1623
  have eq7714 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7695
  have eq21332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1654 eq833
    | exact resolve eq833 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq21341 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq21332
       have r₂ := eq27
       grind)
    | exact resolve eq21332 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21332
  have eq21524 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq21341 eq741
    | exact resolve eq741 eq21341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq21637 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (τ (σ x)) (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq21341 eq2648
    | exact resolve eq2648 eq21341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648 eq21341
  have eq21734 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq21637
    | exact resolve eq21637 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21637
  have eq21819 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq21524
    | exact resolve eq21524 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21524
  have eq21855 : ∀ X0 : G, (M.op X0 X0) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2239 eq21734
    | (have j1 := eq2239 (M.op x (k x x)) x X0
       grind)
    | exact resolve eq21734 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21734
  have eq21911 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21819 X0
       have j1 := eq730 X0 X0 x
       grind)
    | (have r₁ := eq21819 (M.op X0 X0)
       have r₂ := eq730 X0 x (k (M.op X0 X0) x)
       grind)
    | (have r₁ := eq21819 X0
       have r₂ := eq730 y x x
       grind)
    | exact resolve eq21819 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21819
  have eq21930 : (k x x) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq2239 eq21855
    | (have j1 := eq2239 x x y
       grind)
    | exact resolve eq21855 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21855
  have eq21981 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq21911 eq21930
    | exact resolve eq21930 eq21911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21930
  have eq22024 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq7714 x x
       grind)
    | (have r₁ := eq21981
       have r₂ := eq7714 x x
       grind)
    | (have r₁ := eq21981
       have r₂ := eq7714 y x
       grind)
    | exact resolve eq21981 eq7714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7714 eq21981
  have eq22090 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2335 X0 x
       have i₂ := eq21911 x
       grind)
    | exact superpose eq21911 eq2335
    | (have j0 := eq2335 X0 x
       grind)
    | (have r₁ := eq2335 X0 x
       have r₂ := eq21911 x
       grind)
    | exact resolve eq2335 eq21911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21911
  have eq22108 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq22090 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22090
  have eq22424 : ∀ X0 X1 : G, (M.op x (k (M.op X1 X1) X0)) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq825 X1 X0 X0
       have i₂ := eq22108 X0
       grind)
    | exact superpose eq22108 eq825
    | (have j0 := eq825 X1 X0 x
       grind)
    | exact resolve eq825 eq22108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22453 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2343 X0 x x
       have i₂ := eq22108 (M.op x x)
       grind)
    | exact superpose eq22108 eq2343
    | exact resolve eq2343 eq22108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq22470 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2466 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq22108 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq22108 eq2466
    | exact resolve eq2466 eq22108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22517 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22108 eq22470
    | exact resolve eq22470 eq22108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22470
  have eq22531 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22453 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22453
    | (have j0 := eq22453 X0
       grind)
    | exact resolve eq22453 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22453
  have eq22553 : ∀ X0 X1 : G, (M.op x (k x X0)) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq22108 eq22424
    | (have j0 := eq22424 X0 X1
       grind)
    | exact resolve eq22424 eq22108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22424
  have eq22758 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22517
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22517
    | exact resolve eq22517 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22517
  have eq22781 : ∀ X0 X1 : G, (M.op x (k x X0)) = X0 ∨ x = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq22108 eq22553
    | (have j0 := eq22553 X0 (M.op X1 X1)
       grind)
    | exact resolve eq22553 eq22108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22553
  have eq22921 : ∀ X0 : G, (M.op x (k x X0)) = X0 ∨ x = X0 ∨ (M.op x x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22108 eq22781
    | (have j0 := eq22781 X0 x
       grind)
    | exact resolve eq22781 eq22108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22108 eq22781
  have eq23009 : ∀ X0 : G, (M.op x (k x X0)) = X0 ∨ x = X0 ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22024 eq22921
    | (have j0 := eq22921 X0
       grind)
    | exact resolve eq22921 eq22024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22024 eq22921
  have eq23010 : ∀ X0 : G, (M.op x (k x X0)) = X0 ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq23009 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23009
  have eq23046 : ∀ X0 : G, (M.op (σ x) (k (σ x) X0)) = X0 ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22758 eq23010
    | (have j0 := eq23010 X0
       grind)
    | exact resolve eq23010 eq22758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23010
  have eq23054 : ∀ X0 : G, (M.op (σ x) (k (σ x) X0)) = X0 ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22758 eq23046
    | (have j0 := eq23046 X0
       grind)
    | exact resolve eq23046 eq22758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23046
  have eq23059 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq22758 eq31
    | exact resolve eq31 eq22758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22758
  have eq23095 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq23059
    | exact resolve eq23059 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23059
  have eq23096 : x = (σ x) ∨ x = y := by grind
  clear eq23095
  have eq23098 : (σ x) = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq23096
       grind)
    | exact superpose eq23096 eq22
    | exact resolve eq22 eq23096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23100 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq23096
       grind)
    | exact superpose eq23096 eq39
    | exact resolve eq39 eq23096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq23101 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (σ x) (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq23096
       grind)
    | exact superpose eq23096 eq175
    | exact resolve eq175 eq23096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq25854 : (σ (σ (M.op x y))) = (k (σ (σ y)) (σ x)) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1654 eq23100
    | exact resolve eq23100 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654 eq23100
  have eq25882 : (σ (σ (M.op x y))) = (k (σ (σ y)) (σ x)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq25854
  have eq25908 : (σ (σ (M.op x y))) = (k (σ (σ y)) (σ x)) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq23096 eq25882
    | exact resolve eq25882 eq23096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25882
  have eq25909 : (σ (σ (M.op x y))) = (k (σ (σ x)) (σ x)) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq22531 eq25908
    | (have j1 := eq22531 y
       grind)
    | exact resolve eq25908 eq22531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22531 eq25908
  have eq25910 : (k (σ x) (σ x)) = (σ (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq23098 eq25909
    | exact resolve eq25909 eq23098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25909
  have eq25962 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq197 eq23101
    | exact resolve eq23101 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq23101
  have eq33181 : (k x x) = (τ (σ (σ (M.op x y)))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq25910 eq97
    | exact resolve eq97 eq25910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25910
  have eq33206 : (σ (M.op x y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq33181
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq33181
    | exact resolve eq33181 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33181
  have eq33213 : (σ x) = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq23096 eq33206
    | exact resolve eq33206 eq23096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33206
  have eq33242 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq702 X0 y
       have i₂ := eq33213
       grind)
    | exact superpose eq33213 eq702
    | exact resolve eq702 eq33213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33244 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq732 y X0
       have i₂ := eq33213
       grind)
    | exact superpose eq33213 eq732
    | exact resolve eq732 eq33213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq33213
  have eq33820 : ∀ X0 : G, (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq33242 eq97
    | (have j1 := eq33242 X0
       grind)
    | exact resolve eq97 eq33242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33242
  have eq33845 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq28 eq33820
    | (have j0 := eq33820 X0
       grind)
    | exact resolve eq33820 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33820
  have eq33851 : ∀ X0 : G, (M.op x y) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq23096 eq33845
    | (have j0 := eq33845 X0
       grind)
    | exact resolve eq33845 eq23096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33845
  have eq35283 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op x y))) = X0 ∨ (σ x) = (M.op X1 X1) ∨ x = y ∨ (k X2 (σ x)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2241 X0 X1 X2
       have i₂ := eq33244 (k X0 X0)
       grind)
    | exact superpose eq33244 eq2241
    | (have j0 := eq2241 (σ x) X1 X1
       have j1 := eq33244 X2
       grind)
    | exact resolve eq2241 eq33244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241
  have eq35284 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ x = y ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2335 X0 X1
       have i₂ := eq33244 (k X1 X1)
       grind)
    | exact superpose eq33244 eq2335
    | (have j0 := eq2335 X0 (σ x)
       have j1 := eq33244 X1
       grind)
    | (have r₁ := eq2335 X0 (σ x)
       have r₂ := eq33244 (σ x)
       grind)
    | exact resolve eq2335 eq33244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35299 : ∀ X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (k X1 (σ x)) = X1 := by
    intro X1
    first
    | (have j0 := eq35284 x X1
       have j1 := eq730 x X1 (σ x)
       grind)
    | (have r₁ := eq35284 x X1
       have r₂ := eq730 x X1 (σ x)
       grind)
    | (have r₁ := eq35284 x (M.op x x)
       have r₂ := eq730 x X1 (k (M.op x x) (σ x))
       grind)
    | exact resolve eq35284 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35284
  have eq35300 : ∀ X0 X2 : G, (k X2 (σ x)) = X2 ∨ x = y ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq35283 X0 x X2
       have j1 := eq730 X0 X2 (σ x)
       grind)
    | (have r₁ := eq35283 (M.op X0 X0) x X2
       have r₂ := eq730 X0 x (k (M.op X0 X0) (σ (M.op x y)))
       grind)
    | (have r₁ := eq35283 X0 X0 X2
       have r₂ := eq730 X0 x (σ x)
       grind)
    | (have r₁ := eq35283 X0 x (M.op X0 X0)
       have r₂ := eq730 X0 x (k (M.op X0 X0) (σ x))
       grind)
    | exact resolve eq35283 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35283
  have eq35368 : ∀ X0 X1 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (k X0 (σ x)) = X0 ∨ x = y ∨ (σ x) = (M.op X1 X1) := by
    intro X0 X1
    first
    | exact superpose eq33851 eq33244
    | (have j0 := eq33244 X0
       have j1 := eq33851 X1
       grind)
    | exact resolve eq33244 eq33851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33244 eq33851
  have eq35385 : ∀ X0 X1 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35368 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35368
  have eq35400 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq35385 X0 x
       have j1 := eq730 X0 X0 (σ x)
       grind)
    | (have r₁ := eq35385 (M.op X0 X0) x
       have r₂ := eq730 X0 x (k (M.op X0 X0) (σ x))
       grind)
    | (have r₁ := eq35385 X0 X0
       have r₂ := eq730 X0 x (σ x)
       grind)
    | exact resolve eq35385 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq35385
  have eq35430 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq35400 eq2335
    | (have j0 := eq2335 X0 (σ x)
       grind)
    | (have r₁ := eq2335 X0 (σ x)
       have r₂ := eq35400 (σ x)
       grind)
    | exact resolve eq2335 eq35400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35400
  have eq35467 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq35430 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35430
  have eq39597 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ x = y ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2335 X0 X1
       have i₂ := eq35300 (k X1 X1) x
       grind)
    | exact superpose eq35300 eq2335
    | (have j0 := eq2335 X0 (σ x)
       have j1 := eq35300 X1 x
       grind)
    | (have r₁ := eq2335 X0 (σ x)
       have r₂ := eq35300 X0 (σ x)
       grind)
    | (have r₁ := eq2335 X0 (σ (M.op x y))
       have r₂ := eq35300 (σ (M.op x y)) x
       grind)
    | exact resolve eq2335 eq35300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35300
  have eq39634 : ∀ X0 X1 : G, (M.op X0 X0) = (σ x) ∨ x = y ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39597 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39597
  have eq39666 : ∀ X0 X1 : G, (k X1 (M.op x y)) = X1 ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq35467 eq39634
    | (have j0 := eq39634 X0 X1
       have j1 := eq35467 X0
       grind)
    | exact resolve eq39634 eq35467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35467 eq39634
  have eq39800 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y ∨ (σ x) = (M.op X1 X1) := by
    intro X0 X1
    first
    | exact superpose eq39666 eq2335
    | (have j0 := eq2335 X0 (M.op x y)
       have j1 := eq39666 X1 X1
       grind)
    | (have r₁ := eq2335 X0 (M.op x y)
       have r₂ := eq39666 X0 (M.op x y)
       grind)
    | exact resolve eq2335 eq39666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335 eq39666
  have eq39828 : ∀ X0 X1 : G, (σ x) = (M.op X1 X1) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq39800 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39800
  have eq40126 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (σ (σ (σ x)))) ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq2341 X0 x
       have i₂ := eq39828 X2 x
       grind)
    | (have i₁ := eq2341 X0 X0
       have i₂ := eq39828 X0 x
       grind)
    | exact superpose eq39828 eq2341
    | (have j1 := eq39828 X2 x
       grind)
    | exact resolve eq2341 eq39828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341
  have eq40274 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X0 (M.op X1 X1))) = X0 ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq39828 X2 X0
       grind)
    | (have i₁ := eq16 X0 X0 X2
       have i₂ := eq39828 X0 X1
       grind)
    | exact superpose eq39828 eq16
    | (have j1 := eq39828 X2 X1
       grind)
    | exact resolve eq16 eq39828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40329 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4092 sF2 sF2
       have i₂ := eq39828 X0 (M.op sF2 sF2)
       grind)
    | (have i₁ := eq4092 sF2 sF2
       have i₂ := eq39828 (M.op sF2 sF2) x
       grind)
    | exact superpose eq39828 eq4092
    | (have j1 := eq39828 X0 x
       grind)
    | exact resolve eq4092 eq39828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4092
  have eq40362 : ∀ X0 : G, (M.op x y) ≠ (σ x) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq39828 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40415 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq39828 eq40329
    | (have j0 := eq40329 X0
       have j1 := eq39828 X0 x
       grind)
    | exact resolve eq40329 eq39828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40329
  have eq40460 : ∀ X0 X2 : G, (M.op (σ x) (M.op X0 (σ x))) = X0 ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X0 X2
    first
    | exact superpose eq39828 eq40274
    | (have j0 := eq40274 X0 x X2
       have j1 := eq39828 X2 x
       grind)
    | exact resolve eq40274 eq39828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40274
  have eq40594 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (σ (σ (σ (σ x)))) ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X2
    first
    | exact superpose eq2239 eq40126
    | (have j0 := eq40126 x X2
       have j1 := eq2239 (M.op x y) x X2
       grind)
    | exact resolve eq40126 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40126
  have eq40853 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (σ (σ (σ x))) ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X2
    first
    | exact superpose eq23098 eq40594
    | (have j0 := eq40594 X2
       grind)
    | exact resolve eq40594 eq23098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40594
  have eq41021 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (σ (σ x)) ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X2
    first
    | exact superpose eq23098 eq40853
    | (have j0 := eq40853 X2
       grind)
    | exact resolve eq40853 eq23098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40853
  have eq41122 : ∀ X2 : G, (σ x) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X2
    first
    | exact superpose eq23098 eq41021
    | (have j0 := eq41021 X2
       grind)
    | exact resolve eq41021 eq23098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41021
  have eq43463 : ∀ X0 X1 : G, (M.op y (k (M.op X1 X1) (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) ∨ (M.op x y) = (M.op X1 X1) ∨ (M.op x y) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq25962 eq825
    | (have j0 := eq825 X1 (M.op x y) x
       grind)
    | exact resolve eq825 eq25962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq25962
  have eq43485 : ∀ X1 : G, (M.op y (k (M.op X1 X1) (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (M.op x y) = (M.op X1 X1) ∨ (M.op x y) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq39828 eq43463
    | (have j0 := eq43463 x X1
       have j1 := eq39828 X1 X1
       grind)
    | exact resolve eq43463 eq39828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43463
  have eq43505 : ∀ X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op y (k (σ x) (M.op x y))) ∨ (M.op x y) = (M.op X1 X1) ∨ (M.op x y) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq39828 eq43485
    | (have j0 := eq43485 X1
       have j1 := eq39828 X1 X1
       grind)
    | exact resolve eq43485 eq39828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43485
  have eq43523 : ∀ X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op y (k (σ x) (M.op x y))) ∨ (M.op x y) = (M.op X1 X1) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq39828 eq43505
    | (have j0 := eq43505 X1
       have j1 := eq39828 X1 X1
       grind)
    | exact resolve eq43505 eq39828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43505
  have eq43534 : ∀ X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op y (k (σ x) (M.op x y))) ∨ (M.op x y) = (M.op X1 X1) ∨ (M.op x y) = (σ x) ∨ x = y := by
    intro X1
    first
    | exact superpose eq39828 eq43523
    | (have j0 := eq43523 X1
       have j1 := eq39828 X1 X1
       grind)
    | exact resolve eq43523 eq39828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43523
  have eq43540 : ∀ X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op y (k (σ x) (M.op x y))) ∨ (M.op x y) = (M.op X1 X1) ∨ x = y := by
    intro X1
    first
    | (have j0 := eq43534 X1
       have j1 := eq40362 X1
       grind)
    | (have r₁ := eq43534 X1
       have r₂ := eq40362 x
       grind)
    | exact resolve eq43534 eq40362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40362 eq43534
  have eq43544 : ∀ X1 : G, (M.op (σ y) (σ y)) = (M.op y (k (σ x) (M.op x y))) ∨ (M.op x y) = (M.op X1 X1) ∨ x = y := by
    intro X1
    first
    | exact superpose eq40415 eq43540
    | (have j0 := eq43540 X1
       have j1 := eq40415 X1
       grind)
    | exact resolve eq43540 eq40415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40415 eq43540
  have eq43547 : ∀ X1 : G, (k (M.op x y) (M.op x y)) = (M.op y (k (σ x) (M.op x y))) ∨ (M.op x y) = (M.op X1 X1) ∨ x = y := by
    intro X1
    first
    | exact superpose eq2239 eq43544
    | (have j0 := eq43544 X1
       have j1 := eq2239 (M.op x y) X1 X1
       grind)
    | exact resolve eq43544 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239 eq43544
  have eq43550 : ∀ X1 : G, (σ x) = (M.op y (k (σ x) (M.op x y))) ∨ (M.op x y) = (M.op X1 X1) ∨ x = y := by
    intro X1
    first
    | exact superpose eq41122 eq43547
    | (have j0 := eq43547 X1
       have j1 := eq41122 X1
       grind)
    | exact resolve eq43547 eq41122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41122 eq43547
  have eq60262 : ∀ X0 X1 : G, (k (σ x) (M.op x y)) = (M.op (σ x) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op X1 X1) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq43550 eq16
    | (have j1 := eq43550 X1
       grind)
    | exact resolve eq16 eq43550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43550
  have eq60280 : ∀ X1 : G, (k (σ x) (M.op x y)) = (M.op (σ x) (M.op y (σ x))) ∨ (M.op x y) = (M.op X1 X1) ∨ x = y := by
    intro X1
    first
    | exact superpose eq39828 eq60262
    | (have j0 := eq60262 x X1
       have j1 := eq39828 X1 X1
       grind)
    | exact resolve eq60262 eq39828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39828 eq60262
  have eq60288 : ∀ X1 : G, (M.op x y) = (M.op X1 X1) ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq40460 eq60280
    | (have j0 := eq60280 X1
       have j1 := eq40460 x X1
       grind)
    | exact resolve eq60280 eq40460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40460 eq60280
  have eq60620 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op X1 X1))) = X0 ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq60288 X0
       grind)
    | exact superpose eq60288 eq16
    | exact resolve eq16 eq60288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60679 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 X0)) ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2466 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq60288 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq60288 eq2466
    | exact resolve eq2466 eq60288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466
  have eq60680 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op x y) X1) ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2399 X0 X1 (M.op (σ (M.op X0 X0)) X1)
       have i₂ := eq60288 (M.op (σ (M.op X0 X0)) X1)
       grind)
    | exact superpose eq60288 eq2399
    | exact resolve eq2399 eq60288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq60844 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op (σ (M.op x y)) X1) ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq60288 eq60680
    | exact resolve eq60680 eq60288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60680
  have eq60845 : (M.op x y) = (σ (M.op x y)) ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq60288 eq60679
    | exact resolve eq60679 eq60288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60679
  have eq60891 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = X0 ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq60288 eq60620
    | exact resolve eq60620 eq60288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60620
  have eq61123 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op (σ (M.op x y)) X1) ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq20 eq60844
    | (have j0 := eq60844 X1
       grind)
    | exact resolve eq60844 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60844
  have eq61124 : y = (k (σ x) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq60845
    | exact resolve eq60845 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60845
  have eq70896 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x (σ (M.op x y))) (M.op X0 X0)))) ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq61123 eq4091
    | exact resolve eq4091 eq61123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4091 eq61123
  have eq70983 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x (σ (M.op x y))) (M.op x y)))) ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq60288 eq70896
    | exact resolve eq70896 eq60288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60288 eq70896
  have eq71236 : y = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq60891 eq70983
    | exact resolve eq70983 eq60891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70983
  have eq71384 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq61124 eq71236
    | exact resolve eq71236 eq61124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61124 eq71236
  have eq71496 : x = y ∨ y = (k (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq60891 eq71384
    | exact resolve eq71384 eq60891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60891 eq71384
  have eq71497 : y = (k (σ x) (M.op x y)) ∨ x = y := by grind
  clear eq71496
  have eq71581 : (σ y) = (k (σ (σ x)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq71497 eq41
    | exact resolve eq41 eq71497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq71588 : (σ y) = (k (σ (σ x)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq71581
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq71581
    | exact resolve eq71581 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71581
  have eq71592 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq23098 eq71588
    | exact resolve eq71588 eq23098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23098 eq71588
  have eq209457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq71592 eq23054
    | (have j0 := eq23054 (σ (M.op x y))
       grind)
    | exact resolve eq23054 eq71592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23054
  have eq209601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq209457
  have eq209687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq209601
    | exact resolve eq209601 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209601
  have eq209733 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq209687
       have r₂ := eq27
       grind)
    | exact resolve eq209687 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209687
  have eq209816 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq209733 eq31
    | exact resolve eq31 eq209733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq209733
  have eq210001 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq209816
    | exact resolve eq209816 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209816
  have eq210002 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq210001
  have eq210024 : (M.op x y) = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq210002 eq28
    | exact resolve eq28 eq210002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq210031 : (k x (M.op x y)) = (τ (k (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq210002 eq99
    | exact resolve eq99 eq210002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq210034 : (k (M.op x y) x) = (τ (k (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq210002 eq131
    | exact resolve eq131 eq210002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq210057 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = y ∨ (k X0 (σ x)) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq210002 eq35299
    | (have j0 := eq35299 X0
       grind)
    | (have r₁ := eq35299 x
       have r₂ := eq210002
       grind)
    | exact resolve eq35299 eq210002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35299
  have eq210094 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq210002 eq71592
    | exact resolve eq71592 eq210002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71592 eq210002
  have eq210109 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by grind
  clear eq210094
  have eq210146 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = y ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq210057 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210057
  have eq210147 : ∀ X0 : G, x = y ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq210146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210146
  have eq210181 : (k x x) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq97 eq210034
    | exact resolve eq210034 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210034
  have eq210184 : (k x x) = (k x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq97 eq210031
    | exact resolve eq210031 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq210031
  have eq210191 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq210024
    | exact resolve eq210024 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq210024
  have eq210207 : (k (σ x) (σ x)) = (k (M.op x y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq23096 eq210181
    | exact resolve eq210181 eq23096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210181
  have eq210210 : (k (σ x) (σ x)) = (k (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq23096 eq210184
    | exact resolve eq210184 eq23096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23096 eq210184
  have eq210224 : (σ y) = (k (M.op x y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq210109 eq210207
    | exact resolve eq210207 eq210109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210207
  have eq210226 : y = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq71497 eq210210
    | exact resolve eq210210 eq71497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71497 eq210210
  have eq210235 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq210147 eq210224
    | exact resolve eq210224 eq210147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210147 eq210224
  have eq210236 : y = (σ y) ∨ x = y := by
    first
    | exact superpose eq210109 eq210226
    | exact resolve eq210226 eq210109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210109 eq210226
  have eq210238 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq210235 eq210236
    | exact resolve eq210236 eq210235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210235 eq210236
  have eq210834 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq210238
  have eq210835 : x = y := by
    first
    | (have r₁ := eq210834
       have r₂ := eq210191
       grind)
    | exact resolve eq210834 eq210191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210191 eq210834
  have eq210847 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq210835
       grind)
    | exact superpose eq210835 eq18
    | exact resolve eq18 eq210835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq210848 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq210835
       grind)
    | exact superpose eq210835 eq24
    | exact resolve eq24 eq210835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq210835
  have eq210870 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq210848
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq210848
    | exact resolve eq210848 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq210848
  have eq210872 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq210870 eq26
    | exact resolve eq26 eq210870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq210870
  have eq211022 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq702 X0 x
       have i₂ := eq210847
       grind)
    | exact superpose eq210847 eq702
    | exact resolve eq702 eq210847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211093 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2344 X0 x
       have i₂ := eq210847
       grind)
    | exact superpose eq210847 eq2344
    | exact resolve eq2344 eq210847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344 eq210847
  have eq211469 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq211093
    | (have j0 := eq211093 X0
       grind)
    | exact resolve eq211093 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq211093
  have eq211581 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq211469 x
       have i₂ := eq211022 x
       grind)
    | exact superpose eq211022 eq211469
    | exact resolve eq211469 eq211022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211469
  have eq212025 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq210872 eq702
    | exact resolve eq702 eq210872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq210872
  have eq212546 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq212025 x
       have i₂ := eq211022 x
       grind)
    | exact superpose eq211022 eq212025
    | exact resolve eq212025 eq211022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211022 eq212025
  have eq213012 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq212546 eq27
    | exact resolve eq27 eq212546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq212546
  have eq213134 : False := by grind
  exact eq213134

/-- `Equation1496`: `x = (y ◇ x) ◇ (y ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_y_pxx_pxy_Equation1496 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1496 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1496.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
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
  have eq175 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
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
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X1 (M.op X2 X2)) (M.op X1 X0) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
       have i₂ := eq16 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 X1))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
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
  have eq250 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq229
    | exact resolve eq229 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq348 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq398 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq38
    | exact resolve eq38 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq398 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq398
    | exact resolve eq398 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq450 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq348 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq348
    | exact resolve eq348 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq472 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq450 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq450
    | exact resolve eq450 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq701 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq179 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq702 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq702 X1 X0
       grind)
    | exact superpose eq702 eq13
    | (have j0 := eq13 X2 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq702 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X0
       have r₂ := eq702 X0 X1
       grind)
    | exact resolve eq13 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq702 X0 X1
       grind)
    | (have i₁ := eq174 X1
       have i₂ := eq702 X1 X0
       grind)
    | exact superpose eq702 eq174
    | exact resolve eq174 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq739 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 (M.op X1 X1) X1 X2
       have i₂ := eq702 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq179 (M.op X1 X1) X1 X2
       have i₂ := eq702 (M.op X1 X1) X0
       grind)
    | exact superpose eq702 eq179
    | exact resolve eq179 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq472 X1
       have i₂ := eq702 X0 (σ X1)
       grind)
    | (have i₁ := eq472 X1
       have i₂ := eq702 (σ X1) X0
       grind)
    | exact superpose eq702 eq472
    | exact resolve eq472 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq742 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq430 X1
       have i₂ := eq702 X0 (τ X1)
       grind)
    | (have i₁ := eq430 X1
       have i₂ := eq702 (τ X1) X0
       grind)
    | exact superpose eq702 eq430
    | exact resolve eq430 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 : G, x = (k (τ (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq250
       have i₂ := eq702 X0 sF2
       grind)
    | (have i₁ := eq250
       have i₂ := eq702 sF2 x
       grind)
    | exact superpose eq702 eq250
    | exact resolve eq250 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq778 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ (M.op X1 X1))
       have i₂ := eq742 X1 (τ X0)
       grind)
    | exact superpose eq742 eq38
    | exact resolve eq38 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq778 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq778
    | exact resolve eq778 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq825 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (k X0 (M.op X1 X1))) = X2 ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq11 X0 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (M.op X0 X2) (k X0 (M.op X1 X1))) X2
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op y y) := by
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
  have eq833 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq843 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op X1 X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq791 (τ X0) X1
       grind)
    | exact superpose eq791 eq38
    | exact resolve eq38 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq791
  have eq950 : ∀ X0 X1 : G, (k (σ (σ (σ (M.op X1 X1)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq937 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq937
    | exact resolve eq937 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq1178 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X0 X0) (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq430 X2
       have i₂ := eq701 (τ X2) X0 X1
       grind)
    | exact superpose eq701 eq430
    | exact resolve eq430 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq701
  have eq1550 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq843 X1
       have i₂ := eq702 X0 X1
       grind)
    | (have i₁ := eq843 X0
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq843
    | exact resolve eq843 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1567 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq843 X0
       grind)
    | exact superpose eq843 eq702
    | (have j1 := eq843 X0
       grind)
    | exact resolve eq702 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1623 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1651 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq830
       grind)
    | exact superpose eq830 eq40
    | exact resolve eq40 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq830
  have eq1652 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1651
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1651
    | exact resolve eq1651 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq1654 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1652
    | exact resolve eq1652 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq2239 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq702 X2 X1
       have i₂ := eq1550 X2 X0
       grind)
    | exact superpose eq1550 eq702
    | (have j1 := eq1550 X1 X0
       grind)
    | exact resolve eq702 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2241 : ∀ X0 X1 X2 : G, (k (k X0 X0) X2) = X2 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq732 X1 X2
       have i₂ := eq1550 X1 X0
       grind)
    | exact superpose eq1550 eq732
    | (have j1 := eq1550 X1 X0
       grind)
    | exact resolve eq732 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2324 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X1 (σ (M.op X1 X1))
       have i₂ := eq1550 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq1550 eq742
    | (have j1 := eq1550 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq742 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2325 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) ∨ (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1178 X1 X2 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       have i₂ := eq1550 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact superpose eq1550 eq1178
    | (have j1 := eq1550 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact resolve eq1178 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq2327 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) ∨ (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq950 (σ (σ (σ (M.op X1 X1)))) X1
       have i₂ := eq1550 X0 (σ (σ (σ (M.op X1 X1))))
       grind)
    | exact superpose eq1550 eq950
    | (have j1 := eq1550 X0 (σ (σ (σ (M.op X1 X1))))
       grind)
    | exact resolve eq950 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq2329 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X1 (τ (M.op X1 X1))
       have i₂ := eq1550 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1550 eq741
    | (have j1 := eq1550 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq741 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2335 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1550 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2339 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329
  have eq2341 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq2327 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327
  have eq2343 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2325 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325
  have eq2344 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2324 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2324
  have eq2395 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 x
       have i₂ := eq2344 x X0
       grind)
    | exact superpose eq2344 eq16
    | exact resolve eq16 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2399 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X2) X3) X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq179 X2 x X3
       have i₂ := eq2344 x X0
       grind)
    | exact superpose eq2344 eq179
    | exact resolve eq179 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2504 : ∀ X0 X1 : G, (k x (M.op X1 X1)) = (τ (k (σ x) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (M.op X1 X1)
       have i₂ := eq2344 X0 X1
       grind)
    | exact superpose eq2344 eq44
    | exact resolve eq44 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq2519 : ∀ X0 X1 : G, (k x (M.op X1 X1)) = (k x (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq90 eq2504
    | exact resolve eq2504 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq2504
  have eq2648 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (τ (M.op X0 X0)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq739 X1 X2 (M.op X1 X1)
       have i₂ := eq2339 (M.op X1 X1) X0
       grind)
    | exact superpose eq2339 eq739
    | exact resolve eq739 eq2339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq2339
  have eq4089 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op X0 (M.op (M.op x X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 x
       have i₂ := eq177 X0 x x X1
       grind)
    | (have i₁ := eq175 (M.op x x)
       have i₂ := eq177 x x x x
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4090 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op (σ x) X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x
       have i₂ := eq177 X0 sF2 x x
       grind)
    | (have i₁ := eq176 (M.op sF2 sF2)
       have i₂ := eq177 sF2 sF2 x sF2
       grind)
    | exact superpose eq177 eq176
    | exact resolve eq176 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq177
  have eq7692 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1623 X1
       have i₂ := eq1567 X1 X0
       grind)
    | exact superpose eq1567 eq1623
    | (have j0 := eq1623 X1
       have j1 := eq1567 X1 X1
       grind)
    | (have r₁ := eq1623 (M.op X1 X1)
       have r₂ := eq1567 (M.op X1 X1) X1
       grind)
    | exact resolve eq1623 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567 eq1623
  have eq7711 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7692 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7692
  have eq21329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1654 eq833
    | exact resolve eq833 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq21338 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq21329
       have r₂ := eq27
       grind)
    | exact resolve eq21329 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21329
  have eq21521 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq21338 eq741
    | exact resolve eq741 eq21338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq21527 : x = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq21338 eq747
    | exact resolve eq747 eq21338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq21634 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (τ (σ x)) (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq21338 eq2648
    | exact resolve eq2648 eq21338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648 eq21338
  have eq21731 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq21634
    | exact resolve eq21634 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21634
  have eq21814 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq21527
    | exact resolve eq21527 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21527
  have eq21816 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq21521
    | exact resolve eq21521 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21521
  have eq21852 : ∀ X0 : G, (M.op X0 X0) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2239 eq21731
    | (have j1 := eq2239 (M.op x (k x x)) x X0
       grind)
    | exact resolve eq21731 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21731
  have eq21906 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq730 x x x
       grind)
    | (have r₁ := eq21814
       have r₂ := eq730 y x x
       grind)
    | exact resolve eq21814 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21814
  have eq21908 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21816 X0
       have j1 := eq730 X0 X0 x
       grind)
    | (have r₁ := eq21816 (M.op X0 X0)
       have r₂ := eq730 X0 x (k x (M.op X0 X0))
       grind)
    | (have r₁ := eq21816 X0
       have r₂ := eq730 y x x
       grind)
    | exact resolve eq21816 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21816
  have eq21927 : (k x x) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq2239 eq21852
    | (have j1 := eq2239 x x y
       grind)
    | exact resolve eq21852 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21852
  have eq21978 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq21908 eq21927
    | exact resolve eq21927 eq21908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21927
  have eq22021 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq7711 x x
       grind)
    | (have r₁ := eq21978
       have r₂ := eq7711 x x
       grind)
    | (have r₁ := eq21978
       have r₂ := eq7711 y x
       grind)
    | exact resolve eq21978 eq7711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7711 eq21978
  have eq22087 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k x (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2519 X0 X1
       have i₂ := eq21908 (τ (M.op X0 X0))
       grind)
    | exact superpose eq21908 eq2519
    | exact resolve eq2519 eq21908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq22093 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2335 X0 x
       have i₂ := eq21908 x
       grind)
    | exact superpose eq21908 eq2335
    | (have j0 := eq2335 X0 x
       grind)
    | (have r₁ := eq2335 X0 x
       have r₂ := eq21908 x
       grind)
    | exact resolve eq2335 eq21908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22098 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq21908 x
       grind)
    | exact superpose eq21908 eq39
    | exact resolve eq39 eq21908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21908
  have eq22104 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq22093 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22093
  have eq22113 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22098
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22098
    | exact resolve eq22098 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22098
  have eq22119 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22104 eq22087
    | exact resolve eq22087 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22087
  have eq22130 : ∀ X0 : G, x = (τ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq21906 eq22119
    | exact resolve eq22119 eq21906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21906 eq22119
  have eq22138 : x = (τ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22104 eq22130
    | exact resolve eq22130 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22130
  have eq22148 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 x
       have i₂ := eq22138
       grind)
    | exact superpose eq22138 eq14
    | exact resolve eq14 eq22138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22138
  have eq22149 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22148
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22148
    | exact resolve eq22148 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22148
  have eq22155 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq22149 eq31
    | exact resolve eq31 eq22149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22191 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq22155
    | exact resolve eq22155 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22155
  have eq22192 : x = (σ x) ∨ x = y := by grind
  clear eq22191
  have eq22193 : (M.op x y) = (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq22192
       grind)
    | exact superpose eq22192 eq18
    | exact resolve eq18 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22194 : (σ x) = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq22192
       grind)
    | exact superpose eq22192 eq22
    | exact resolve eq22 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22195 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (σ x) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq22192
       grind)
    | exact superpose eq22192 eq35
    | exact resolve eq35 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq22196 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq22192
       grind)
    | exact superpose eq22192 eq39
    | exact resolve eq39 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq22197 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (σ x) (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq22192
       grind)
    | exact superpose eq22192 eq175
    | exact resolve eq175 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq22400 : ∀ X1 : G, x = (k X1 X1) ∨ x = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq1550 x X1
       have i₂ := eq22104 x
       grind)
    | exact superpose eq22104 eq1550
    | exact resolve eq1550 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq22427 : ∀ X1 X2 : G, (M.op (M.op (M.op (σ x) X1) X2) X1) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq2399 x X1 X2
       have i₂ := eq22104 x
       grind)
    | exact superpose eq22104 eq2399
    | exact resolve eq2399 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq22556 : ∀ X0 X1 : G, (M.op x (k X0 (M.op X1 X1))) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 X1 X0
       have i₂ := eq22104 X0
       grind)
    | exact superpose eq22104 eq825
    | (have j0 := eq825 X0 X1 x
       grind)
    | exact resolve eq825 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22585 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2343 X0 x x
       have i₂ := eq22104 (M.op x x)
       grind)
    | exact superpose eq22104 eq2343
    | exact resolve eq2343 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq22606 : y = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4089 x x
       have i₂ := eq22104 (M.op x x)
       grind)
    | exact superpose eq22104 eq4089
    | exact resolve eq4089 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089
  have eq22648 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22021 eq22606
    | exact resolve eq22606 eq22021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22606
  have eq22666 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22585 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22585
    | (have j0 := eq22585 X0
       grind)
    | exact resolve eq22585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22585
  have eq22688 : ∀ X0 X1 : G, (M.op x (k X0 x)) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq22104 eq22556
    | (have j0 := eq22556 X0 X1
       grind)
    | exact resolve eq22556 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22556
  have eq22803 : ∀ X1 X2 : G, (M.op (M.op (M.op (σ x) X1) X2) X1) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq22427 X1 X2
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22427
    | (have j0 := eq22427 X1 X2
       grind)
    | exact resolve eq22427 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22427
  have eq22830 : ∀ X1 : G, (σ x) = (k X1 X1) ∨ x = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq22149 eq22400
    | (have j0 := eq22400 X1
       grind)
    | exact resolve eq22400 eq22149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22400
  have eq22937 : y = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22149 eq22648
    | exact resolve eq22648 eq22149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22648
  have eq22964 : ∀ X0 X1 : G, (M.op x (k X0 x)) = X0 ∨ x = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq22104 eq22688
    | (have j0 := eq22688 X0 (M.op X1 X1)
       grind)
    | exact resolve eq22688 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22688
  have eq23074 : ∀ X1 : G, (σ x) = (k X1 X1) ∨ (σ x) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq22149 eq22830
    | (have j0 := eq22830 X1
       grind)
    | exact resolve eq22830 eq22149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22830
  have eq23161 : ∀ X0 : G, (M.op x (k X0 x)) = X0 ∨ x = X0 ∨ (M.op x x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22104 eq22964
    | (have j0 := eq22964 X0 x
       grind)
    | exact resolve eq22964 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22964
  have eq23285 : ∀ X0 : G, (M.op x (k X0 x)) = X0 ∨ x = X0 ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22021 eq23161
    | (have j0 := eq23161 X0
       grind)
    | exact resolve eq23161 eq22021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22021 eq23161
  have eq23286 : ∀ X0 : G, (M.op x (k X0 x)) = X0 ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq23285 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23285
  have eq23343 : ∀ X0 : G, (M.op (σ x) (k X0 (σ x))) = X0 ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22149 eq23286
    | (have j0 := eq23286 X0
       grind)
    | exact resolve eq23286 eq22149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23286
  have eq23361 : ∀ X0 : G, (M.op (σ x) (k X0 (σ x))) = X0 ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22149 eq23343
    | (have j0 := eq23343 X0
       grind)
    | exact resolve eq23343 eq22149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23343
  have eq25612 : (σ (σ (M.op x y))) = (k (σ x) (σ (σ y))) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1654 eq22195
    | exact resolve eq22195 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654 eq22195
  have eq25634 : (σ (σ (M.op x y))) = (k (σ x) (σ (σ y))) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq25612
  have eq25658 : (σ (σ (M.op x y))) = (k (σ x) (σ (σ y))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq22192 eq25634
    | exact resolve eq25634 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25634
  have eq25661 : (σ (σ (M.op x y))) = (k (σ x) (σ (σ x))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq22666 eq25658
    | (have j1 := eq22666 y
       grind)
    | exact resolve eq25658 eq22666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22666 eq25658
  have eq25662 : (k (σ x) (σ x)) = (σ (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq22194 eq25661
    | exact resolve eq25661 eq22194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25661
  have eq25835 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq197 eq22197
    | exact resolve eq22197 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq27243 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq115
       have i₂ := eq23074 sF3
       grind)
    | exact superpose eq23074 eq115
    | (have j1 := eq23074 (σ y)
       grind)
    | exact resolve eq115 eq23074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq23074
  have eq27246 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27243
  have eq27298 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq27246
    | exact resolve eq27246 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27246
  have eq27345 : (σ x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22149 eq27298
    | exact resolve eq27298 eq22149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22149 eq27298
  have eq27455 : ∀ X0 : G, y ≠ (σ x) ∨ (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2335 X0 y
       have i₂ := eq27345
       grind)
    | exact superpose eq27345 eq2335
    | (have j0 := eq2335 X0 y
       grind)
    | exact resolve eq2335 eq27345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27345
  have eq27462 : y ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22104 eq27455
    | exact resolve eq27455 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27455
  have eq27463 : y ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq27462
  have eq27856 : (k x x) = (τ (σ (σ (M.op x y)))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq25662 eq97
    | exact resolve eq97 eq25662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25662
  have eq27878 : (σ (M.op x y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq27856
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq27856
    | exact resolve eq27856 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27856
  have eq27885 : (σ x) = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq22192 eq27878
    | exact resolve eq27878 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27878
  have eq27912 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq702 y X0
       have i₂ := eq27885
       grind)
    | exact superpose eq27885 eq702
    | exact resolve eq702 eq27885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27914 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq732 y X0
       have i₂ := eq27885
       grind)
    | exact superpose eq27885 eq732
    | exact resolve eq732 eq27885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq28085 : y = (M.op (M.op x y) (M.op (σ x) (σ x))) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq22197 y
       have i₂ := eq27885
       grind)
    | exact superpose eq27885 eq22197
    | exact resolve eq22197 eq27885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22197 eq27885
  have eq28100 : y = (M.op (M.op x y) (M.op (σ x) (σ x))) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq28085
  have eq28485 : ∀ X0 : G, (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq27912 eq97
    | (have j1 := eq27912 X0
       grind)
    | exact resolve eq97 eq27912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq28507 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq28 eq28485
    | (have j0 := eq28485 X0
       grind)
    | exact resolve eq28485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28485
  have eq28513 : ∀ X0 : G, (M.op x y) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq22192 eq28507
    | (have j0 := eq28507 X0
       grind)
    | exact resolve eq28507 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28507
  have eq30184 : ∀ X0 X1 X2 : G, (k (σ (M.op x y)) X0) = X0 ∨ (M.op X1 X1) = (σ x) ∨ x = y ∨ (k (σ x) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2241 X0 X1 X2
       have i₂ := eq27914 (k X0 X0)
       grind)
    | exact superpose eq27914 eq2241
    | (have j0 := eq2241 (σ x) X1 X2
       have j1 := eq27914 X2
       grind)
    | exact resolve eq2241 eq27914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241
  have eq30198 : ∀ X0 X2 : G, (k (σ x) X2) = X2 ∨ x = y ∨ (k (σ (M.op x y)) X0) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq30184 X0 x X2
       have j1 := eq730 X0 X2 (σ x)
       grind)
    | (have r₁ := eq30184 (M.op X0 X0) x X2
       have r₂ := eq730 X0 x (k (σ (M.op x y)) (M.op X0 X0))
       grind)
    | (have r₁ := eq30184 X0 X0 X2
       have r₂ := eq730 X0 x (σ x)
       grind)
    | (have r₁ := eq30184 X0 x (M.op X0 X0)
       have r₂ := eq730 X0 x (k (σ x) (M.op X0 X0))
       grind)
    | exact resolve eq30184 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30184
  have eq30265 : ∀ X0 X1 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (k (σ x) X0) = X0 ∨ x = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq28513 eq27914
    | (have j0 := eq27914 X0
       have j1 := eq28513 X1
       grind)
    | exact resolve eq27914 eq28513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27914 eq28513
  have eq30280 : ∀ X0 X1 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (k (σ x) X0) = X0 ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq30265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30265
  have eq30294 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq30280 X0 x
       have j1 := eq730 X0 X0 (σ x)
       grind)
    | (have r₁ := eq30280 (M.op X0 X0) x
       have r₂ := eq730 X0 x (k (σ x) (M.op X0 X0))
       grind)
    | (have r₁ := eq30280 X0 X0
       have r₂ := eq730 X0 x (σ x)
       grind)
    | exact resolve eq30280 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq30280
  have eq30340 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30294 eq2335
    | (have j0 := eq2335 X0 (σ x)
       grind)
    | (have r₁ := eq2335 X0 (σ x)
       have r₂ := eq30294 (σ x)
       grind)
    | exact resolve eq2335 eq30294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30294
  have eq30355 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq30340 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30340
  have eq34439 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ x = y ∨ (k (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2335 X0 X1
       have i₂ := eq30198 (k X1 X1) x
       grind)
    | exact superpose eq30198 eq2335
    | (have j0 := eq2335 X0 (σ x)
       have j1 := eq30198 X1 x
       grind)
    | (have r₁ := eq2335 X0 (σ x)
       have r₂ := eq30198 X0 (σ x)
       grind)
    | (have r₁ := eq2335 X0 (σ (M.op x y))
       have r₂ := eq30198 (σ (M.op x y)) x
       grind)
    | exact resolve eq2335 eq30198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30198
  have eq34454 : ∀ X0 X1 : G, (M.op X0 X0) = (σ x) ∨ x = y ∨ (k (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34439 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34439
  have eq34478 : ∀ X0 X1 : G, (k (M.op x y) X1) = X1 ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq30355 eq34454
    | (have j0 := eq34454 X0 X1
       have j1 := eq30355 X0
       grind)
    | exact resolve eq34454 eq30355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30355 eq34454
  have eq34622 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq34478 eq2335
    | (have j0 := eq2335 X0 (M.op x y)
       have j1 := eq34478 X1 X1
       grind)
    | (have r₁ := eq2335 X0 (M.op x y)
       have r₂ := eq34478 X0 (M.op x y)
       grind)
    | exact resolve eq2335 eq34478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335 eq34478
  have eq34639 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq34622 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34622
  have eq34954 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (σ (σ (σ x)))) ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq2341 X0 x
       have i₂ := eq34639 X2 x
       grind)
    | (have i₁ := eq2341 X0 X0
       have i₂ := eq34639 X0 x
       grind)
    | exact superpose eq34639 eq2341
    | (have j1 := eq34639 X2 x
       grind)
    | exact resolve eq2341 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341
  have eq35102 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X0 (M.op X1 X1))) = X0 ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq34639 X2 X0
       grind)
    | (have i₁ := eq16 X0 X0 X2
       have i₂ := eq34639 X0 X1
       grind)
    | exact superpose eq34639 eq16
    | (have j1 := eq34639 X2 X1
       grind)
    | exact resolve eq16 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35156 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4090 sF2 sF2
       have i₂ := eq34639 X0 (M.op sF2 sF2)
       grind)
    | (have i₁ := eq4090 sF2 sF2
       have i₂ := eq34639 (M.op sF2 sF2) x
       grind)
    | exact superpose eq34639 eq4090
    | (have j1 := eq34639 X0 x
       grind)
    | exact resolve eq4090 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4090
  have eq35183 : ∀ X0 : G, (M.op x y) ≠ (σ x) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34639 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35221 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34639 eq35156
    | (have j0 := eq35156 X0
       have j1 := eq34639 X0 x
       grind)
    | exact resolve eq35156 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35156
  have eq35265 : ∀ X0 X2 : G, (M.op (σ x) (M.op X0 (σ x))) = X0 ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X0 X2
    first
    | exact superpose eq34639 eq35102
    | (have j0 := eq35102 X0 x X2
       have j1 := eq34639 X2 x
       grind)
    | exact resolve eq35102 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35102
  have eq35400 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (σ (σ (σ (σ x)))) ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X2
    first
    | exact superpose eq2239 eq34954
    | (have j0 := eq34954 x X2
       have j1 := eq2239 (M.op x y) x X2
       grind)
    | exact resolve eq34954 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34954
  have eq35656 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (σ (σ (σ x))) ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X2
    first
    | exact superpose eq22194 eq35400
    | (have j0 := eq35400 X2
       grind)
    | exact resolve eq35400 eq22194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35400
  have eq35823 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (σ (σ x)) ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X2
    first
    | exact superpose eq22194 eq35656
    | (have j0 := eq35656 X2
       grind)
    | exact resolve eq35656 eq22194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35656
  have eq35922 : ∀ X2 : G, (σ x) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (M.op X2 X2) = (M.op x y) := by
    intro X2
    first
    | exact superpose eq22194 eq35823
    | (have j0 := eq35823 X2
       grind)
    | exact resolve eq35823 eq22194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22194 eq35823
  have eq36859 : ∀ X0 X1 : G, (M.op y (k (M.op x y) (M.op X1 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) ∨ (M.op X1 X1) = (M.op x y) ∨ (M.op x y) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq25835 eq825
    | (have j0 := eq825 (M.op x y) X1 x
       grind)
    | exact resolve eq825 eq25835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq25835
  have eq36877 : ∀ X1 : G, (M.op y (k (M.op x y) (M.op X1 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (M.op X1 X1) = (M.op x y) ∨ (M.op x y) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq34639 eq36859
    | (have j0 := eq36859 x X1
       have j1 := eq34639 X1 X1
       grind)
    | exact resolve eq36859 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36859
  have eq36893 : ∀ X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op y (k (M.op x y) (σ x))) ∨ (M.op X1 X1) = (M.op x y) ∨ (M.op x y) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq34639 eq36877
    | (have j0 := eq36877 X1
       have j1 := eq34639 X1 X1
       grind)
    | exact resolve eq36877 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36877
  have eq36908 : ∀ X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op y (k (M.op x y) (σ x))) ∨ (M.op X1 X1) = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X1
    first
    | exact superpose eq34639 eq36893
    | (have j0 := eq36893 X1
       have j1 := eq34639 X1 X1
       grind)
    | exact resolve eq36893 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36893
  have eq36918 : ∀ X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op y (k (M.op x y) (σ x))) ∨ (M.op X1 X1) = (M.op x y) ∨ (M.op x y) = (σ x) ∨ x = y := by
    intro X1
    first
    | exact superpose eq34639 eq36908
    | (have j0 := eq36908 X1
       have j1 := eq34639 X1 X1
       grind)
    | exact resolve eq36908 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36908
  have eq36926 : ∀ X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op y (k (M.op x y) (σ x))) ∨ (M.op X1 X1) = (M.op x y) ∨ x = y := by
    intro X1
    first
    | (have j0 := eq36918 X1
       have j1 := eq35183 X1
       grind)
    | (have r₁ := eq36918 X1
       have r₂ := eq35183 x
       grind)
    | exact resolve eq36918 eq35183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35183 eq36918
  have eq36930 : ∀ X1 : G, (M.op (σ y) (σ y)) = (M.op y (k (M.op x y) (σ x))) ∨ (M.op X1 X1) = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq35221 eq36926
    | (have j0 := eq36926 X1
       have j1 := eq35221 X1
       grind)
    | exact resolve eq36926 eq35221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35221 eq36926
  have eq36933 : ∀ X1 : G, (k (M.op x y) (M.op x y)) = (M.op y (k (M.op x y) (σ x))) ∨ (M.op X1 X1) = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq2239 eq36930
    | (have j0 := eq36930 X1
       have j1 := eq2239 (M.op x y) X1 X1
       grind)
    | exact resolve eq36930 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239 eq36930
  have eq36936 : ∀ X1 : G, (σ x) = (M.op y (k (M.op x y) (σ x))) ∨ (M.op X1 X1) = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq35922 eq36933
    | (have j0 := eq36933 X1
       have j1 := eq35922 X1
       grind)
    | exact resolve eq36933 eq35922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35922 eq36933
  have eq41347 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq22193 eq22803
    | exact resolve eq22803 eq22193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22193 eq22803
  have eq41515 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq41347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41347
  have eq42167 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op (M.op x y) X0) (σ (M.op X1 X1)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq41515 eq2395
    | exact resolve eq2395 eq41515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395 eq41515
  have eq42190 : ∀ X0 : G, y = (M.op X0 (M.op (M.op (M.op x y) X0) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22104 eq42167
    | exact resolve eq42167 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42167
  have eq42237 : ∀ X0 : G, y = (M.op X0 (M.op (M.op (M.op x y) X0) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq42190 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42190
    | (have j0 := eq42190 X0
       grind)
    | exact resolve eq42190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42190
  have eq46327 : ∀ X0 X1 : G, (k (M.op x y) (σ x)) = (M.op (σ x) (M.op y (M.op X0 X0))) ∨ (M.op X1 X1) = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq36936 eq16
    | (have j1 := eq36936 X1
       grind)
    | exact resolve eq16 eq36936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36936
  have eq46341 : ∀ X1 : G, (k (M.op x y) (σ x)) = (M.op (σ x) (M.op y (σ x))) ∨ (M.op X1 X1) = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq34639 eq46327
    | (have j0 := eq46327 x X1
       have j1 := eq34639 X1 X1
       grind)
    | exact resolve eq46327 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34639 eq46327
  have eq46348 : ∀ X1 : G, y = (k (M.op x y) (σ x)) ∨ (M.op X1 X1) = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq35265 eq46341
    | (have j0 := eq46341 X1
       have j1 := eq35265 x X1
       grind)
    | exact resolve eq46341 eq35265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35265 eq46341
  have eq46364 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq46348 eq22196
    | (have j1 := eq46348 X0
       grind)
    | exact resolve eq22196 eq46348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22196 eq46348
  have eq46367 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq46364 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46364
  have eq46373 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq46367
    | (have j0 := eq46367 X0
       grind)
    | exact resolve eq46367 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46367
  have eq46376 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq46373 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46373
    | (have j0 := eq46373 X0
       grind)
    | exact resolve eq46373 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46373
  have eq58864 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq46376 eq23361
    | (have j0 := eq23361 (σ (M.op x y))
       have j1 := eq46376 X0
       grind)
    | exact resolve eq23361 eq46376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23361 eq46376
  have eq58904 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq58864 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58864
  have eq58931 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq58904
    | (have j0 := eq58904 X0
       grind)
    | exact resolve eq58904 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58904
  have eq58945 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq58931 X0
       grind)
    | (have r₁ := eq58931 X0
       have r₂ := eq27
       grind)
    | exact resolve eq58931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58931
  have eq59385 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28100
       have i₂ := eq58945 sF2
       grind)
    | exact superpose eq58945 eq28100
    | exact resolve eq28100 eq58945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28100 eq58945
  have eq59419 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq59385
  have eq59495 : y = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27912 eq59419
    | exact resolve eq59419 eq27912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27912 eq59419
  have eq59813 : x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq59495
       have r₂ := eq27463
       grind)
    | exact resolve eq59495 eq27463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27463 eq59495
  have eq60080 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq22113 eq59813
    | exact resolve eq59813 eq22113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22113 eq59813
  have eq60081 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq60080
  have eq60298 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq60081 eq31
    | exact resolve eq31 eq60081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60081
  have eq60373 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq60298
    | exact resolve eq60298 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60298
  have eq60374 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq60373
  have eq60389 : (M.op x y) = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq60374 eq28
    | exact resolve eq28 eq60374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq60374
  have eq60474 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq60389
    | exact resolve eq60389 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60389
  have eq60499 : (M.op x y) = (σ x) ∨ y = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq60474
       have i₂ := eq22192
       grind)
    | exact superpose eq22192 eq60474
    | exact resolve eq60474 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60500 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq60474
       grind)
    | exact superpose eq60474 eq18
    | exact resolve eq18 eq60474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60538 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq22192
       have i₂ := eq60474
       grind)
    | exact superpose eq60474 eq22192
    | exact resolve eq22192 eq60474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60551 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq60538 eq60499
    | exact resolve eq60499 eq60538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60499 eq60538
  have eq60552 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq60551
  have eq60558 : x = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq60552 eq29
    | exact resolve eq29 eq60552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq60897 : (σ x) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq22192 eq60558
    | exact resolve eq60558 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22192 eq60558
  have eq60923 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq60552 eq60897
    | exact resolve eq60897 eq60552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60897
  have eq61938 : y = (M.op y (M.op (M.op x y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq60500 eq42237
    | exact resolve eq42237 eq60500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42237 eq60500
  have eq61952 : y = (M.op y (M.op (M.op x y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq61938
  have eq61958 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22937 eq61952
    | exact resolve eq61952 eq22937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22937 eq61952
  have eq61962 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22104 eq61958
    | exact resolve eq61958 eq22104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22104 eq61958
  have eq61963 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq61962
  have eq61965 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq60552 eq61963
    | exact resolve eq61963 eq60552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60552 eq61963
  have eq61969 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq61965 eq31
    | exact resolve eq31 eq61965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq61965
  have eq62074 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq60923 eq61969
    | exact resolve eq61969 eq60923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60923 eq61969
  have eq62207 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq62074
  have eq62208 : x = y := by
    first
    | (have r₁ := eq62207
       have r₂ := eq60474
       grind)
    | exact resolve eq62207 eq60474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60474 eq62207
  have eq62220 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq62208
       grind)
    | exact superpose eq62208 eq18
    | exact resolve eq18 eq62208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq62221 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq62208
       grind)
    | exact superpose eq62208 eq24
    | exact resolve eq24 eq62208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq62208
  have eq62241 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq62221
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62221
    | exact resolve eq62221 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq62221
  have eq62243 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq62241 eq26
    | exact resolve eq26 eq62241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq62241
  have eq62335 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq702 x X0
       have i₂ := eq62220
       grind)
    | exact superpose eq62220 eq702
    | exact resolve eq702 eq62220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62400 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2344 X0 x
       have i₂ := eq62220
       grind)
    | exact superpose eq62220 eq2344
    | exact resolve eq2344 eq62220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344 eq62220
  have eq62621 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq62400
    | (have j0 := eq62400 X0
       grind)
    | exact resolve eq62400 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq62400
  have eq62724 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq62621 x
       have i₂ := eq62335 x
       grind)
    | exact superpose eq62335 eq62621
    | exact resolve eq62621 eq62335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62621
  have eq63080 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq62243 eq702
    | exact resolve eq702 eq62243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq62243
  have eq63418 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63080 x
       have i₂ := eq62335 x
       grind)
    | exact superpose eq62335 eq63080
    | exact resolve eq63080 eq62335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62335 eq63080
  have eq63776 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq63418 eq27
    | exact resolve eq27 eq63418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq63418
  have eq63838 : False := by grind
  exact eq63838

/-- `Equation1496`: `x = (y ◇ x) ◇ (y ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pxy_Equation1496 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1496 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1496.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
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
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
       have i₂ := eq16 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (k X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq179
    | exact resolve eq179 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq183 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq175
    | exact resolve eq175 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq187 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq445 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq323
    | exact resolve eq323 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq583 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq183 (τ X0)
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq183
    | exact resolve eq183 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq646 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 X1 (M.op (k X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 (k X1 X1) X2
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq646 X0 X1 X2
       have i₂ := eq174 X2
       grind)
    | exact superpose eq174 eq646
    | exact resolve eq646 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq666 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (k X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 (τ X0) X1 X2
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq187
    | exact resolve eq187 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 x x
       have i₂ := eq652 X1 x x
       grind)
    | (have i₁ := eq652 X0 X1 X1
       have i₂ := eq652 (k X1 X1) X1 x
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 x (k X1 X1) X2
       have i₂ := eq652 X0 X1 x
       grind)
    | (have i₁ := eq187 X0 (k X0 X0) X2
       have i₂ := eq652 (k X0 X0) X1 X2
       grind)
    | exact superpose eq652 eq187
    | exact resolve eq187 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq721 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq714 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq714
    | exact resolve eq714 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 X2 X1 X1
       have i₂ := eq698 X1 X0
       grind)
    | (have i₁ := eq187 X2 X1 X1
       have i₂ := eq698 X0 X1
       grind)
    | exact superpose eq698 eq187
    | exact resolve eq187 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq187 X2 x (k X2 X2)
       have i₂ := eq698 (M.op x (k X2 X2)) X0
       grind)
    | (have i₁ := eq187 X2 x (k X2 X2)
       have i₂ := eq698 X0 (M.op x (k X2 X2))
       grind)
    | exact superpose eq698 eq187
    | exact resolve eq187 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq773 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq757
    | exact resolve eq757 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq807 : ∀ X0 X2 : G, (k X0 X0) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq187 X2 x (k X2 X2)
       have i₂ := eq763 (M.op x (k X2 X2)) X0
       grind)
    | exact superpose eq763 eq187
    | exact resolve eq187 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq825 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq763 X0 (σ X1)
       grind)
    | exact superpose eq763 eq10
    | exact resolve eq10 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X1 X1
       have i₂ := eq763 X0 (τ X1)
       grind)
    | exact superpose eq763 eq445
    | exact resolve eq445 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq828 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq763 X0 (τ X1)
       grind)
    | exact superpose eq763 eq34
    | exact resolve eq34 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq763
  have eq829 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq828
    | exact resolve eq828 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq846 : ∀ X0 X1 : G, (k X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq829
    | exact resolve eq829 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq960 : ∀ X0 X2 : G, (σ (k X0 X0)) = (σ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq825 x X2
       have i₂ := eq825 x X0
       grind)
    | exact superpose eq825 eq825
    | exact resolve eq825 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq825
    | exact resolve eq825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (M.op (σ (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X2 X1 (M.op (k X1 X1) X2)
       have i₂ := eq825 (M.op (k X1 X1) X2) X0
       grind)
    | exact superpose eq825 eq180
    | exact resolve eq180 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq825
  have eq1156 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq846 x X1
       have i₂ := eq846 X0 x
       grind)
    | exact superpose eq846 eq846
    | exact resolve eq846 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq1293 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = y := by
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
  have eq1300 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq1308 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1300
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1300
    | exact resolve eq1300 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1312 : (M.op x y) = (k x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1293
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1293
    | exact resolve eq1293 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1623 : ∀ X0 X2 : G, (σ (σ (k X0 X0))) = (τ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq827 x X2
       have i₂ := eq969 X0 x
       grind)
    | exact superpose eq969 eq827
    | exact resolve eq827 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq969
  have eq2048 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq960 X1 x
       have i₂ := eq1156 X0 x
       grind)
    | exact superpose eq1156 eq960
    | exact resolve eq960 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq1156
  have eq7816 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1312
       grind)
    | exact superpose eq1312 eq40
    | exact resolve eq40 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1312
  have eq7817 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq7816
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7816
    | exact resolve eq7816 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7816
  have eq7819 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq7817
    | exact resolve eq7817 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7817
  have eq12450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq7819 eq1308
    | exact resolve eq1308 eq7819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq7819
  have eq12457 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq12450
       have r₂ := eq27
       grind)
    | exact resolve eq12450 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12450
  have eq12464 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq12457 eq97
    | exact resolve eq97 eq12457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq12457
  have eq12687 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq12464
    | exact resolve eq12464 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12464
  have eq12688 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12687
  have eq12783 : ∀ X0 X1 : G, (M.op (M.op y X0) (k X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq721 X1 x X0
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq721
    | exact resolve eq721 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq12787 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq773 X0 X1 x
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq773
    | exact resolve eq773 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq12789 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq807 X0 x
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq807
    | exact resolve eq807 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq12803 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ y) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq996 x X0 X1
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq996
    | exact resolve eq996 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq12844 : ∀ X0 : G, (τ (k X0 X0)) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1623 x X0
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq1623
    | exact resolve eq1623 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq12853 : ∀ X0 : G, (σ (k X0 X0)) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2048 x X0
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq2048
    | exact resolve eq2048 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048 eq12688
  have eq12887 : ∀ X0 : G, (σ (k X0 X0)) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12853 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12853
    | (have j0 := eq12853 X0
       grind)
    | exact resolve eq12853 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12853
  have eq12894 : ∀ X0 : G, (τ (k X0 X0)) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12844 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12844
    | (have j0 := eq12844 X0
       grind)
    | exact resolve eq12844 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12844
  have eq12921 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ y) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq12803 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12803
    | (have j0 := eq12803 X0 X1
       grind)
    | exact resolve eq12803 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12803
  have eq12934 : ∀ X1 : G, (M.op y (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq12789 eq12787
    | exact resolve eq12787 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12787
  have eq12936 : ∀ X0 : G, (M.op (M.op y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12789 eq12783
    | exact resolve eq12783 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12783
  have eq12971 : (σ y) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12789 eq12887
    | exact resolve eq12887 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12887
  have eq12975 : (σ (σ y)) = (τ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12789 eq12894
    | exact resolve eq12894 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12894
  have eq12987 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq12789 eq12921
    | exact resolve eq12921 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12921
  have eq13013 : (σ y) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12971
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12971
    | exact resolve eq12971 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12971
  have eq13033 : (σ y) = (σ (τ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12975 eq13013
    | exact resolve eq13013 eq12975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12975 eq13013
  have eq13044 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13033
       have i₂ := eq14 y
       grind)
    | exact superpose eq14 eq13033
    | exact resolve eq13033 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13033
  have eq13060 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq13044 eq31
    | exact resolve eq31 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13087 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq13060
    | exact resolve eq13060 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13060
  have eq13088 : y = (σ y) ∨ x = y := by grind
  clear eq13087
  have eq13090 : (M.op x y) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq13088
       grind)
    | exact superpose eq13088 eq18
    | exact resolve eq18 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13092 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (σ y) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq13088
       grind)
    | exact superpose eq13088 eq36
    | exact resolve eq36 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq13101 : x ≠ (σ y) ∨ x = y := by grind
  have eq15849 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12934 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12934
    | (have j0 := eq12934 x
       grind)
    | exact resolve eq12934 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12934
  have eq15868 : x = (M.op (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13044 eq15849
    | exact resolve eq15849 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15849
  have eq15975 : ∀ X0 : G, (M.op (k y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op y y) = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq12936 X0
       have i₂ := eq11 y X0
       grind)
    | exact superpose eq11 eq12936
    | (have j1 := eq11 y X0
       grind)
    | exact resolve eq12936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12936
  have eq16009 : ∀ X0 : G, (k y y) = X0 ∨ (M.op (k y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq15975 X0
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq15975
    | (have j0 := eq15975 X0
       grind)
    | exact resolve eq15975 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15975
  have eq16028 : ∀ X0 : G, y = X0 ∨ (M.op (k y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq12789 eq16009
    | (have j0 := eq16009 X0
       grind)
    | exact resolve eq16009 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16009
  have eq16029 : ∀ X0 : G, y = X0 ∨ (M.op (k y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16028 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16028
  have eq16047 : ∀ X0 : G, (σ y) = X0 ∨ (M.op (k y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13044 eq16029
    | (have j0 := eq16029 x
       grind)
    | exact resolve eq16029 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16029
  have eq16056 : ∀ X0 : G, (M.op (k (σ y) X0) (σ y)) = X0 ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13044 eq16047
    | (have j0 := eq16047 X0
       grind)
    | exact resolve eq16047 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16047
  have eq17739 : ∀ X0 : G, (k y X0) = (M.op (σ y) X0) ∨ (M.op y y) = X0 ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 y X0
       have i₂ := eq12987 X0
       grind)
    | exact superpose eq12987 eq11
    | (have j0 := eq11 y X0
       grind)
    | exact resolve eq11 eq12987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12987
  have eq17805 : ∀ X0 : G, (k y y) = X0 ∨ (k y X0) = (M.op (σ y) X0) ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17739 X0
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq17739
    | (have j0 := eq17739 X0
       grind)
    | exact resolve eq17739 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17739
  have eq17850 : ∀ X0 : G, y = X0 ∨ (k y X0) = (M.op (σ y) X0) ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12789 eq17805
    | (have j0 := eq17805 X0
       grind)
    | exact resolve eq17805 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17805
  have eq17851 : ∀ X0 : G, y = X0 ∨ (k y X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq17850 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17850
  have eq17885 : ∀ X0 : G, (σ y) = X0 ∨ (k y X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13044 eq17851
    | (have j0 := eq17851 x
       grind)
    | exact resolve eq17851 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17851
  have eq17910 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13044 eq17885
    | (have j0 := eq17885 X0
       grind)
    | exact resolve eq17885 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17885
  have eq49996 : x = (k (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17910 eq15868
    | (have j1 := eq17910 (σ x)
       grind)
    | exact resolve eq15868 eq17910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17910
  have eq50062 : x = (k (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq49996
  have eq50295 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq50062 eq13092
    | exact resolve eq13092 eq50062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13092 eq50062
  have eq50298 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by grind
  clear eq50295
  have eq50302 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq50298
    | exact resolve eq50298 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50298
  have eq50304 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq50302
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50302
    | exact resolve eq50302 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50302
  have eq50307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq50304 eq16056
    | (have j0 := eq16056 (σ (M.op x y))
       grind)
    | exact resolve eq16056 eq50304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16056 eq50304
  have eq50312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq50307
  have eq50315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26 eq50312
    | exact resolve eq50312 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50312
  have eq50319 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq50315
       have r₂ := eq27
       grind)
    | exact resolve eq50315 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50315
  have eq50324 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq50319 eq31
    | exact resolve eq31 eq50319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50319
  have eq50404 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq50324
    | exact resolve eq50324 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50324
  have eq50405 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq50404
  have eq50422 : (M.op x y) = (τ (σ y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq50405 eq28
    | exact resolve eq28 eq50405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq50405
  have eq50453 : (M.op x y) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq50422
    | exact resolve eq50422 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50422
  have eq50469 : y = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq50453 eq31
    | exact resolve eq31 eq50453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50510 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq50453 eq13044
    | exact resolve eq13044 eq50453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13044 eq50453
  have eq50607 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq50510
  have eq50693 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq13088 eq50469
    | exact resolve eq50469 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50469
  have eq50722 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq13088 eq50693
    | exact resolve eq50693 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50693
  have eq50758 : x = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq50607 eq29
    | exact resolve eq29 eq50607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50607
  have eq50874 : x = (τ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13088 eq50758
    | exact resolve eq50758 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50758
  have eq50909 : x = (σ y) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq50722 eq50874
    | exact resolve eq50874 eq50722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50722 eq50874
  have eq50926 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq50909
       have r₂ := eq13101
       grind)
    | exact resolve eq50909 eq13101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101 eq50909
  have eq50944 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq50926 eq31
    | exact resolve eq31 eq50926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq50986 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq50926 eq13090
    | exact resolve eq13090 eq50926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13090
  have eq51000 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq50926 eq15868
    | exact resolve eq15868 eq50926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15868
  have eq51067 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq51000
  have eq51081 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq50986
  have eq51109 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq51067
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq51067
    | exact resolve eq51067 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51067
  have eq51143 : (σ y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13088 eq50944
    | exact resolve eq50944 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13088 eq50944
  have eq51168 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq50926 eq51143
    | exact resolve eq51143 eq50926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51143
  have eq51780 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x (τ (k X0 X0)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq51081 eq666
    | exact resolve eq666 eq51081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq51081
  have eq51792 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq583 eq51780
    | exact resolve eq51780 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq51780
  have eq51887 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq51792
  have eq52536 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq51109 eq12789
    | exact resolve eq12789 eq51109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12789 eq51109
  have eq52609 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by grind
  clear eq52536
  have eq52654 : x = y ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq50926 eq52609
    | exact resolve eq52609 eq50926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50926 eq52609
  have eq52655 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq52654
  have eq52802 : x = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq52655 eq29
    | exact resolve eq29 eq52655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52655
  have eq52922 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq51168 eq52802
    | exact resolve eq52802 eq51168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51168 eq52802
  have eq52943 : x = y := by
    first
    | (have r₁ := eq52922
       have r₂ := eq51887
       grind)
    | exact resolve eq52922 eq51887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51887 eq52922
  have eq52962 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq52943
       grind)
    | exact superpose eq52943 eq18
    | exact resolve eq18 eq52943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq52963 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq52943
       grind)
    | exact superpose eq52943 eq24
    | exact resolve eq24 eq52943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq52943
  have eq52974 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq52963
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52963
    | exact resolve eq52963 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52963
  have eq52975 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq52962
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq52962
    | exact resolve eq52962 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52962
  have eq52979 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq52974 eq26
    | exact resolve eq26 eq52974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq52974
  have eq53040 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq52979
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq52979
    | exact resolve eq52979 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq52979
  have eq53058 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq52975
       grind)
    | exact superpose eq52975 eq39
    | exact resolve eq39 eq52975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq52975
  have eq53329 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq53058
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53058
    | exact resolve eq53058 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53058
  have eq53388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53040 eq53329
    | exact resolve eq53329 eq53040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53040 eq53329
  have eq53428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq53388
    | exact resolve eq53388 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq53388
  have eq53458 : False := by grind
  exact eq53458
