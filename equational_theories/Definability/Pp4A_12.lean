import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1921`: `x = (y ◇ (y ◇ x)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pxy_pyy_pxy_Equation1921 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1921 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1921.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq43 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq42 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq47
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq43 X1 X0
       grind)
    | (have r₁ := eq53 X0 X0
       have r₂ := eq43 X0 X0
       grind)
    | (have r₁ := eq53 X1 X0
       have r₂ := eq43 X0 X1
       grind)
    | exact resolve eq53 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq53
  have eq148 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq155 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq148 X0 X1
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq148 X0 X0
       have r₂ := eq56 X0 X0
       grind)
    | exact resolve eq148 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq148
  have eq328 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq155 (σ X0) (σ X1)
       grind)
    | exact superpose eq155 eq15
    | exact resolve eq15 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X0 X1
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq328
    | exact resolve eq328 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq328
  have eq335 : False := by grind
  exact eq335

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyy_pxy_Equation1924 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X1 X0)) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 (M.op X1 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq273 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq273 (σ X0)
       grind)
    | exact superpose eq273 eq15
    | exact resolve eq15 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq284
    | exact resolve eq284 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq284
  have eq349 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq351 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq349 X0 X1
       have j1 := eq350 X0 X1
       grind)
    | (have r₁ := eq349 X0 X1
       have r₂ := eq350 X0 X1
       grind)
    | exact resolve eq349 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq350
  have eq417 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq351 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq351
    | exact resolve eq351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq459 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq417 X0 X1
       grind)
    | exact superpose eq417 eq61
    | (have j1 := eq417 X0 (M.op (M.op X1 X0) X0)
       grind)
    | exact resolve eq61 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq460 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq417 X0 X1
       grind)
    | exact superpose eq417 eq9
    | (have j1 := eq417 X0 (M.op X1 X0)
       grind)
    | exact resolve eq9 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq762 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq459 X0 X1
       have i₂ := eq460 X0 X1
       grind)
    | exact superpose eq460 eq459
    | (have j0 := eq459 X0 X1
       have j1 := eq460 X0 X1
       grind)
    | exact resolve eq459 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq460
  have eq779 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq762 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq784 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq779 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq779 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq779 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq808 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq784 (σ X1) (σ X0)
       grind)
    | exact superpose eq784 eq15
    | exact resolve eq15 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq808 X0 X1
       have i₂ := eq784 X1 X0
       grind)
    | exact superpose eq784 eq808
    | exact resolve eq808 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq808
  have eq1168 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq835 x y
       grind)
    | exact superpose eq835 eq16
    | (have r₁ := eq16
       have r₂ := eq835 x y
       grind)
    | exact resolve eq16 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq1190 : False := by grind
  exact eq1190

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,X) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxy_y_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X1) (M.op X0 X1)) = X2 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X1) (M.op X0 X1)) = X2 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq52 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq52 X0 X0 X2
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq52 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq274 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 X2)) ≠ (M.op (M.op X0 X0) X3) ∨ (M.op X3 (M.op X0 X0)) = (k X3 (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op X0 X0)
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq12 X0 (M.op X2 X2)
       have i₂ := eq19 X2 X2 X2
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X3 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X2 X2) (M.op X2 X2)
       have r₂ := eq19 X2 X2 X2
       grind)
    | (have r₁ := eq12 (M.op X0 X2) (M.op X0 X0)
       have r₂ := eq19 X0 X0 X2
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq431 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X2) (M.op X2 X3)) ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X1) X2 X3
       have i₂ := eq77 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq77 eq9
    | (have j1 := eq77 (M.op X0 X0) X1 X2
       grind)
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq454 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq431 X0 X1 x x
       have j1 := eq274 X0 X1 x X1
       grind)
    | (have r₁ := eq431 X1 (M.op X1 x) X1 x
       have r₂ := eq274 X1 X1 x (M.op X1 x)
       grind)
    | (have r₁ := eq431 X0 x X1 x
       have r₂ := eq274 X0 X1 x x
       grind)
    | exact resolve eq431 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq431
  have eq2107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq454 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq454
    | exact resolve eq454 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq3325 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2107 (σ X1) (σ X0)
       grind)
    | exact superpose eq2107 eq15
    | exact resolve eq15 eq2107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3340 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3325 X0 X1
       have i₂ := eq2107 X1 X0
       grind)
    | exact superpose eq2107 eq3325
    | exact resolve eq3325 eq2107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107 eq3325
  have eq3356 : False := by grind
  exact eq3356

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pyx_x_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq105 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq105 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq105 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq119 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq95 X0 X1 X2 X3
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq95 X0 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq95 X0 X0 X2 X3
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq95 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq708 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 (M.op X0 X0)
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq21 X1 X1 (M.op X1 X2)
       have i₂ := eq19 X1 X1 X2
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq2897 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X1 X0 x (M.op X1 X0)
       have i₂ := eq119 X1 X0 (M.op X1 X0) (M.op X0 x)
       grind)
    | exact superpose eq119 eq708
    | (have j1 := eq119 X1 X0 x x
       grind)
    | exact resolve eq708 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq708
  have eq2956 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2897 X0 X1
       have j1 := eq109 X0 X1
       grind)
    | (have r₁ := eq2897 X0 X1
       have r₂ := eq109 X0 X1
       grind)
    | (have r₁ := eq2897 X1 X0
       have r₂ := eq109 X0 X1
       grind)
    | exact resolve eq2897 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq2897
  have eq2982 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2956 (σ X0) (σ X1)
       grind)
    | exact superpose eq2956 eq15
    | exact resolve eq15 eq2956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3001 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2982 X0 X1
       have i₂ := eq2956 X0 X1
       grind)
    | exact superpose eq2956 eq2982
    | exact resolve eq2982 eq2956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956 eq2982
  have eq3500 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3001 x y
       grind)
    | exact superpose eq3001 eq16
    | (have r₁ := eq16
       have r₂ := eq3001 x y
       grind)
    | exact resolve eq16 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001
  have eq3565 : False := by grind
  exact eq3565

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X1 (k X1 X1)
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq46 X1 (k X1 X1)
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq54
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq61
  have eq151 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq155 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq151 X1 X1
       have r₂ := eq63 X1 X1
       grind)
    | exact resolve eq151 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq151
  have eq375 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq155 (σ X0) (σ X1)
       grind)
    | exact superpose eq155 eq15
    | exact resolve eq15 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 X1
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq375
    | exact resolve eq375 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq375
  have eq382 : False := by grind
  exact eq382

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pxy_pyy_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq9 X1 (M.op X1 X1) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq22
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq120 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq120 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq120 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq120 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq122
    | exact resolve eq122 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq122
    | exact resolve eq122 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq125 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq124
    | exact resolve eq124 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq126 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq123 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq123
    | exact resolve eq123 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq123
  have eq161 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X2 X1
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq9
    | exact resolve eq9 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq168 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq245 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X3) (M.op X3 X2)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X3 X2
       have i₂ := eq168 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq168 X0 X0
       grind)
    | exact superpose eq168 eq9
    | (have j1 := eq168 X0 X1
       grind)
    | exact resolve eq9 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X2) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq57 X1 X2 X0
       grind)
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq531 : ∀ X0 X3 : G, (M.op X3 X3) = (M.op X3 X0) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq482 x X3 X0 (M.op x x)
       have i₂ := eq245 X0 X3 x x
       grind)
    | exact superpose eq245 eq482
    | (have j1 := eq245 X0 X3 x X3
       grind)
    | exact resolve eq482 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq613 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq531 X0 X1
       grind)
    | (have i₁ := eq168 x x
       have i₂ := eq531 X0 x
       grind)
    | exact superpose eq531 eq168
    | (have j0 := eq168 X0 X1
       have j1 := eq531 X0 X1
       grind)
    | exact resolve eq168 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq614 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X2 X3)) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq245 X0 X1 X3 X2
       have i₂ := eq531 X0 X1
       grind)
    | (have i₁ := eq245 X3 X3 X2 X3
       have i₂ := eq531 X0 X3
       grind)
    | exact superpose eq531 eq245
    | (have j0 := eq245 X0 X1 X2 X3
       have j1 := eq531 X0 X1
       grind)
    | exact resolve eq245 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq531
  have eq632 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X2 X3)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq614 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq633 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq613 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq637 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 X1 x x
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq632
    | (have j0 := eq632 X0 X1 x x
       grind)
    | exact resolve eq632 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq824 : ∀ X0 X1 X2 X3 : G, (τ X1) = (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X2 X3)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq161 X1 X3 X2
       have i₂ := eq633 X0 X1
       grind)
    | (have i₁ := eq161 X0 X1 X2
       have i₂ := eq633 X0 X1
       grind)
    | exact superpose eq633 eq161
    | (have j1 := eq633 X0 X1
       grind)
    | exact resolve eq161 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq860 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1 x x
       have i₂ := eq161 X0 x x
       grind)
    | exact superpose eq161 eq824
    | (have j0 := eq824 X0 X1 x x
       grind)
    | exact resolve eq824 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq824
  have eq932 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq860 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq860
    | (have j0 := eq860 (σ X0) (σ X1)
       grind)
    | exact resolve eq860 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq956 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq932 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq932
    | (have j0 := eq932 X0 X1
       grind)
    | exact resolve eq932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq961 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq956
    | (have j0 := eq956 X0 X1
       grind)
    | exact resolve eq956 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq987 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq961 x y
       grind)
    | exact superpose eq961 eq16
    | (have j1 := eq961 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq961 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq961 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq1007 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq987
       have i₂ := eq637 x y
       grind)
    | exact superpose eq637 eq987
    | (have j1 := eq637 x y
       grind)
    | (have r₁ := eq987
       have r₂ := eq637 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq987
       have r₂ := eq637 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq987 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq987
  have eq1012 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by grind
  clear eq1007
  have eq1013 : x = y := by grind
  clear eq1012
  have eq1017 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1013
       grind)
    | exact superpose eq1013 eq16
    | exact resolve eq16 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1018 : False := by grind
  exact eq1018

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pyx_pxy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq86
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq86
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq106 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq200 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq98 X1
       grind)
    | exact superpose eq98 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq201 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq200
    | (have j0 := eq200 X0 X1
       grind)
    | exact resolve eq200 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq231 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201 y x
       grind)
    | exact superpose eq201 eq16
    | (have j1 := eq201 y x
       grind)
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq659 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq231
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq231
    | (have j1 := eq59 y x
       grind)
    | exact resolve eq231 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq231
  have eq660 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq659
  have eq10521 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq660
       grind)
    | exact superpose eq660 eq10
    | exact resolve eq10 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq10562 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10521
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq10521
    | exact resolve eq10521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10521
  have eq10563 : (M.op y y) = (M.op x x) := by grind
  clear eq10562
  have eq10645 : ∀ X0 : G, y = (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq106 y y x
       have i₂ := eq10563
       grind)
    | exact superpose eq10563 eq106
    | exact resolve eq106 eq10563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq10563
  have eq10688 : x = y := by
    first
    | (have i₁ := eq10645 x
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq10645
    | exact resolve eq10645 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10645
  have eq10812 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10688
       grind)
    | exact superpose eq10688 eq16
    | exact resolve eq16 eq10688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10688
  have eq10813 : False := by grind
  exact eq10813

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq77 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq92 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq131 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq222 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq222 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq222 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq222 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq232 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq131 X0 X0
       have i₂ := eq223 X0
       grind)
    | exact superpose eq223 eq131
    | exact resolve eq131 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq233 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq223 (σ X0)
       grind)
    | exact superpose eq223 eq15
    | exact resolve eq15 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq233 X0
       have i₂ := eq223 X0
       grind)
    | exact superpose eq223 eq233
    | exact resolve eq233 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq235 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq232 X0
       have i₂ := eq223 (τ X0)
       grind)
    | exact superpose eq223 eq232
    | exact resolve eq232 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq232
  have eq290 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq77 (M.op X0 X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq77
    | exact resolve eq77 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 x) (M.op x y))) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 (M.op X0 X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq55
    | exact resolve eq55 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 x) (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq54
    | exact resolve eq54 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq234 (M.op X0 X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq234
    | exact resolve eq234 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (σ (M.op (M.op X0 x) (M.op x y))) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq304 X0
       have i₂ := eq234 X0
       grind)
    | exact superpose eq234 eq304
    | exact resolve eq304 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq321 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 x) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq54 eq290
    | exact resolve eq290 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq323 : ∀ X0 : G, (σ (M.op (M.op X0 x) (M.op x y))) = (M.op (M.op (σ X0) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq320 X0
       have i₂ := eq77 (σ X0)
       grind)
    | exact superpose eq77 eq320
    | exact resolve eq320 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq331 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq77
    | exact resolve eq77 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq395 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq331 eq9
    | exact resolve eq9 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq630 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq64
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq630
    | exact resolve eq630 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq635 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq631
    | exact resolve eq631 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq645 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X0 X3 X4
       have i₂ := eq52 X0 X1 X2
       grind)
    | (have i₁ := eq52 X2 X1 X2
       have i₂ := eq52 X2 X2 X2
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) X1) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) x) (M.op (M.op X0 X0) x)) (M.op (M.op (M.op X0 X0) x) (M.op (M.op X0 X0) x))) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0
       have i₂ := eq52 X0 X1 X2
       grind)
    | (have i₁ := eq77 X2
       have i₂ := eq52 X2 X2 X2
       grind)
    | exact superpose eq52 eq77
    | exact resolve eq77 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X3 (M.op X0 X0)
       have i₂ := eq52 X0 X1 X2
       grind)
    | (have i₁ := eq55 X1 X1 (M.op X1 X2)
       have i₂ := eq52 X1 X1 X2
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq679 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X0) X3 X4
       have i₂ := eq52 X0 X1 X2
       grind)
    | (have i₁ := eq9 (M.op X2 X2) X1 X2
       have i₂ := eq52 X2 X2 X2
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq52 X0 X1 X2
       grind)
    | (have i₁ := eq54 (M.op X2 X2)
       have i₂ := eq52 X2 X2 X2
       grind)
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq234 (M.op X0 X0)
       have i₂ := eq52 X0 X1 X2
       grind)
    | (have i₁ := eq234 (M.op X2 X2)
       have i₂ := eq52 X2 X2 X2
       grind)
    | exact superpose eq52 eq234
    | exact resolve eq234 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (σ (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq685 X0 X1 X2
       have i₂ := eq234 X0
       grind)
    | exact superpose eq234 eq685
    | exact resolve eq685 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq710 : ∀ X0 : G, (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq658 X0
       have i₂ := eq674 sF2 sF2 sF2
       grind)
    | exact superpose eq674 eq658
    | (have j1 := eq674 (σ x) (σ y) X0
       grind)
    | exact resolve eq658 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq711 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq657 X0
       have i₂ := eq674 x x x
       grind)
    | exact superpose eq674 eq657
    | (have j1 := eq674 x y X0
       grind)
    | exact resolve eq657 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq718 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op (M.op (M.op X0 X0) x) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 X1
       have i₂ := eq674 (M.op (M.op X0 X0) x) (M.op (M.op X0 X0) x) (M.op (M.op X0 X0) x)
       grind)
    | exact superpose eq674 eq650
    | exact resolve eq650 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq719 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) x) (M.op x y)) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq649 X0 X1 X2 X3
       have i₂ := eq674 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq674 eq649
    | exact resolve eq649 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq725 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) x) (M.op x y)) = (σ (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq707 X0 X1 X2
       have i₂ := eq674 (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq674 eq707
    | exact resolve eq707 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq729 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq710 eq395
    | exact resolve eq395 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq710
  have eq747 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq711 eq9
    | exact resolve eq9 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq747 eq53
    | exact resolve eq53 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq868 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq729 eq9
    | exact resolve eq9 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1061 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 x) (M.op x y))) (M.op (M.op X0 X0) (M.op (M.op X1 x) (M.op x y)))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 x) (M.op x y))) (M.op (M.op X0 X0) (M.op (M.op X1 x) (M.op x y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq294 eq52
    | exact resolve eq52 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1067 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 x) (M.op x y))) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1061 X0 X1 X2
       have i₂ := eq674 (M.op (M.op X0 X0) (M.op (M.op X1 x) sF0)) (M.op (M.op X0 X0) (M.op (M.op X1 x) sF0)) (M.op (M.op X0 X0) (M.op (M.op X1 x) sF0))
       grind)
    | exact superpose eq674 eq1061
    | exact resolve eq1061 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1280 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq321 eq53
    | exact resolve eq53 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1287 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (M.op (M.op X1 x) (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq321 eq294
    | exact resolve eq294 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq321
  have eq1478 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x X0) (M.op X0 X1)) (M.op (M.op x y) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq674 eq9
    | exact resolve eq9 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1746 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X3) X4)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq674 eq1280
    | exact resolve eq1280 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1801 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) x) := by
    first
    | exact superpose eq814 eq1280
    | exact resolve eq1280 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq1841 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) (M.op X0 X1)) x) := by
    intro X0 X1
    first
    | exact superpose eq674 eq1801
    | exact resolve eq1801 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq2382 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x X0) x) (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq1478 eq1280
    | exact resolve eq1280 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2820 : ∀ X0 : G, (M.op (M.op (σ (M.op (M.op (M.op x X0) x) (M.op x y))) x) (M.op x y)) = (σ (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2382 eq323
    | exact resolve eq323 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq2860 : ∀ X0 : G, (σ (M.op (M.op x X0) (M.op x y))) = (M.op (M.op (M.op (M.op (σ (M.op x X0)) x) (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq323 eq2820
    | exact resolve eq2820 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820
  have eq2866 : ∀ X0 : G, (σ (M.op (M.op x X0) (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq300 eq2860
    | exact resolve eq2860 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq8702 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) x) (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1 x (M.op X0 X1)
       have i₂ := eq674 (M.op X0 X1) (M.op X0 X1) (M.op X1 x)
       grind)
    | exact superpose eq674 eq675
    | exact resolve eq675 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8728 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X2) (M.op X2 X3))) x) (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq674 (M.op (M.op X0 X0) (M.op (M.op X1 X2) (M.op X2 X3))) X1 X4
       have i₂ := eq675 X1 X2 X3 X0
       grind)
    | exact superpose eq675 eq674
    | exact resolve eq674 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq9140 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op x y)) (M.op (M.op x x) (M.op x y))) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq711 eq681
    | exact resolve eq681 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq711
  have eq9210 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op x y)) x) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1287 eq9140
    | exact resolve eq9140 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq9140
  have eq9306 : ∀ X0 : G, (M.op (M.op X0 x) (M.op X0 x)) = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq300 eq9210
    | exact resolve eq9210 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9210
  have eq9429 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 x)
       have i₂ := eq9306 X0
       grind)
    | exact superpose eq9306 eq54
    | exact resolve eq54 eq9306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9306
  have eq9546 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) x) = (M.op (M.op (M.op X0 (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1280 eq9429
    | exact resolve eq9429 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9558 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op X0 x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq9429 eq8702
    | exact resolve eq8702 eq9429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9429
  have eq9621 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 x) x) (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq9546 eq300
    | exact resolve eq300 eq9546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq9675 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op X0 X0) (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq9621 eq674
    | exact resolve eq674 eq9621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9621
  have eq9736 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq1280 eq9675
    | exact resolve eq9675 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9675
  have eq10221 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) (M.op (M.op (M.op X1 X4) X5) X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq679 X0 X1 X4 (M.op (M.op X1 X4) X5) X6
       have i₂ := eq645 (M.op X0 X1) (M.op X1 X4) X5 X2 X3
       grind)
    | (have i₁ := eq679 X0 X1 X4 (M.op (M.op X1 X4) X5) X6
       have i₂ := eq645 (M.op X0 X1) X2 X3 (M.op X1 X4) X5
       grind)
    | exact superpose eq645 eq679
    | exact resolve eq679 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq10222 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) x) (M.op x y)) (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq679 X0 X1 X2 (M.op (M.op X1 X2) X3) X4
       have i₂ := eq674 (M.op X0 X1) (M.op X1 X2) X3
       grind)
    | exact superpose eq674 eq679
    | exact resolve eq679 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq11369 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) (M.op X0 X0)) (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq9558 eq9
    | exact resolve eq9 eq9558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9558
  have eq12945 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X0 (M.op (M.op X1 X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq719 eq719
    | exact resolve eq719 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12963 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X0 X2)) x) (M.op x y)) = (M.op X1 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq719 X1 (M.op X0 X2) (M.op X2 x) X4
       have i₂ := eq52 X0 X2 x
       grind)
    | (have i₁ := eq719 X0 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq52 X0 X1 X2
       grind)
    | exact superpose eq52 eq719
    | exact resolve eq719 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq12968 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X2)) = (M.op (M.op (M.op (M.op X1 X1) (M.op X0 x)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq77 eq719
    | exact resolve eq719 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq13026 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X1) (M.op X0 x)) x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq11369 eq719
    | exact resolve eq719 eq11369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11369
  have eq13068 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op x y) X3)) = (M.op X0 (M.op (M.op x X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq719 eq718
    | exact resolve eq718 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq13077 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X1)) x) (M.op x y)) = (σ (M.op X0 (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq719 eq323
    | exact resolve eq323 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13139 : ∀ X0 X1 X3 : G, x = (M.op (M.op (M.op (M.op (M.op (M.op x (M.op X0 X1)) (M.op x (M.op X0 X1))) X0) x) (M.op x y)) (M.op (M.op x y) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1478 (M.op X0 X1) x X3
       have i₂ := eq719 (M.op x (M.op X0 X1)) X0 X1 x
       grind)
    | exact superpose eq719 eq1478
    | exact resolve eq1478 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq13271 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op (M.op (M.op x (M.op X0 X1)) (M.op x (M.op X0 X1))) X0) x) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13139 X0 X1 x
       have i₂ := eq674 (M.op (M.op (M.op (M.op x (M.op X0 X1)) (M.op x (M.op X0 X1))) X0) x) sF0 x
       grind)
    | exact superpose eq674 eq13139
    | exact resolve eq13139 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13139
  have eq13345 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq13026 eq12968
    | exact resolve eq12968 eq13026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12968 eq13026
  have eq13388 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op (M.op (M.op x (M.op X0 X1)) (M.op x y)) X0) x) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13271 X0 X1
       have i₂ := eq9736 (M.op x (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq9736 eq13271
    | exact resolve eq13271 eq9736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9736 eq13271
  have eq13440 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X1) (M.op X0 X2)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12963 X0 X1 X2 x
       have i₂ := eq13345 X0 X1 x
       grind)
    | exact superpose eq13345 eq12963
    | exact resolve eq12963 eq13345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12963 eq13345
  have eq13533 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X4)) := by
    intro X0 X1 X2 X4
    first
    | exact superpose eq13440 eq8728
    | exact resolve eq8728 eq13440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8728
  have eq13536 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 x)) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq13440 eq1067
    | exact resolve eq1067 eq13440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq15326 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = (M.op X1 (M.op (M.op (σ x) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq868 eq13533
    | exact resolve eq13533 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq15647 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) x) (M.op x y)) = (M.op X0 (M.op (M.op (M.op X1 X3) X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq719 X0 (M.op X1 X3) X4 X5
       have i₂ := eq13533 (M.op X0 X0) X1 X3 X2
       grind)
    | (have i₁ := eq719 X0 (M.op X1 X3) X4 X5
       have i₂ := eq13533 (M.op X0 X0) X1 X2 X3
       grind)
    | exact superpose eq13533 eq719
    | exact resolve eq719 eq13533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15728 : ∀ X0 X1 X3 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X3) X4) X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | exact superpose eq13440 eq15647
    | exact resolve eq15647 eq13440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13440 eq15647
  have eq15769 : ∀ X1 X2 X3 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) x)) = (M.op X1 (M.op (M.op (σ x) X2) X3)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq15326 x x X2 X3
       have i₂ := eq13536 x sF4 (M.op sF3 x)
       grind)
    | exact superpose eq13536 eq15326
    | exact resolve eq15326 eq13536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15326
  have eq15846 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) x) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10222 X0 X1 x x x
       have i₂ := eq15728 (M.op (M.op (M.op X0 X1) x) sF0) X1 x x x
       grind)
    | exact superpose eq15728 eq10222
    | exact resolve eq10222 eq15728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10222
  have eq15853 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10221 X0 X1 X2 X3 x x x
       have i₂ := eq15728 (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) X1 x x x
       grind)
    | exact superpose eq15728 eq10221
    | exact resolve eq10221 eq15728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10221
  have eq18292 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x X0) X1) X2) = (M.op (M.op (M.op (M.op (M.op (M.op x X0) X1) X2) x) (M.op x y)) (M.op (M.op x y) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8702 (M.op (M.op x y) X3) X1
       have i₂ := eq13068 (M.op (M.op (M.op (M.op (M.op x y) X3) X1) x) sF0) X1 X2 X3
       grind)
    | (have i₁ := eq8702 (M.op (M.op x X1) X2) X1
       have i₂ := eq13068 (M.op (M.op (M.op (M.op (M.op x X1) X2) X1) x) sF0) X1 X2 X3
       grind)
    | exact superpose eq13068 eq8702
    | exact resolve eq8702 eq13068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13068
  have eq18363 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X0) X1) X2) = (M.op (M.op (M.op (M.op (M.op (M.op x X0) X1) X2) x) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18292 X0 X1 X2 X2
       have i₂ := eq674 (M.op (M.op (M.op (M.op x X0) X1) X2) x) sF0 X2
       grind)
    | exact superpose eq674 eq18292
    | exact resolve eq18292 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18292
  have eq18480 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x (M.op X0 X1)) (M.op x y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq18363 eq13388
    | exact resolve eq13388 eq18363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13388 eq18363
  have eq28229 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op (M.op x (M.op X0 X1)) (M.op x y))) x) (M.op x y)) = (σ (M.op x (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq18480 eq725
    | exact resolve eq725 eq18480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq18480
  have eq28640 : ∀ X0 X1 X2 : G, (σ (M.op x (M.op X0 X2))) = (M.op (M.op (M.op (σ (M.op x (M.op X0 X1))) (σ (M.op x (M.op X0 X1)))) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2866 eq28229
    | exact resolve eq28229 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866 eq28229
  have eq28740 : ∀ X0 X1 X2 : G, (σ (M.op x (M.op X0 X2))) = (σ (M.op x (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq28640
    | exact resolve eq28640 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28640
  have eq32025 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) x) (M.op x y)) (M.op (M.op X0 X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8702 (M.op (M.op X1 X2) X3) X1
       have i₂ := eq12945 (M.op (M.op (M.op (M.op (M.op X1 X2) X3) X1) x) sF0) X1 X2 X3 X4 X5
       grind)
    | (have i₁ := eq8702 (M.op (M.op X1 X4) X5) X1
       have i₂ := eq12945 (M.op (M.op (M.op (M.op (M.op X1 X4) X5) X1) x) sF0) X1 X2 X3 X4 X5
       grind)
    | exact superpose eq12945 eq8702
    | exact resolve eq8702 eq12945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8702 eq12945
  have eq55925 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1) x) (M.op x y)) (M.op (M.op X0 X4) X5)) = X0 := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq1746 X0 (M.op X1 X2) x X4 X5
       have i₂ := eq719 (M.op X0 (M.op X1 X2)) X1 X2 x
       grind)
    | exact superpose eq719 eq1746
    | exact resolve eq1746 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq1746
  have eq56527 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq32025 eq55925
    | exact resolve eq55925 eq32025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32025 eq55925
  have eq56821 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 x)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56527 X0 X1 X2
       have i₂ := eq13536 (M.op X0 (M.op X1 X2)) X0 (M.op X1 X2)
       grind)
    | exact superpose eq13536 eq56527
    | exact resolve eq56527 eq13536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13536 eq56527
  have eq57246 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X3)) X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56821 X0 X1 X2
       have i₂ := eq13533 (M.op X0 (M.op X1 X2)) X0 x X3
       grind)
    | (have i₁ := eq56821 X0 X1 X2
       have i₂ := eq13533 (M.op X0 (M.op X1 X2)) X0 X3 x
       grind)
    | exact superpose eq13533 eq56821
    | exact resolve eq56821 eq13533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13533 eq56821
  have eq57937 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X5)) (M.op (M.op X1 X2) X3)) = X0 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq57246 X0 (M.op (M.op X1 X2) X3) x X5
       have i₂ := eq15728 X0 X1 X2 X3 x
       grind)
    | exact superpose eq15728 eq57246
    | exact resolve eq57246 eq15728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15728 eq57246
  have eq119623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq635
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq635
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq635 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq119623
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119623
    | exact resolve eq119623 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119623
  have eq119672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq119669
    | exact resolve eq119669 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119669
  have eq119673 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq119672
       have r₂ := eq27
       grind)
    | exact resolve eq119672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119672
  have eq119674 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq119673
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119673
    | exact resolve eq119673 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119673
  have eq119783 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) X1) X2)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq119674 eq57937
    | exact resolve eq57937 eq119674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119674
  have eq119792 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) x)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq15769 eq119783
    | (have j0 := eq119783 X0 (σ y) x
       grind)
    | exact resolve eq119783 eq15769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119783
  have eq119830 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq729 eq119792
    | exact resolve eq119792 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119792
  have eq119867 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq119830 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq119830
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq119830
       grind)
    | exact resolve eq12 eq119830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119830
  have eq119966 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq119867
  have eq119993 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq64 eq119966
    | exact resolve eq119966 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119966
  have eq120004 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq119993
    | exact resolve eq119993 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119993
  have eq120007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq120004
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq120004
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq120004 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120004
  have eq120047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq120007
  have eq120054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq120047
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120047
    | exact resolve eq120047 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120047
  have eq120057 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq120054
    | exact resolve eq120054 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120054
  have eq120058 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq120057
       have r₂ := eq27
       grind)
    | exact resolve eq120057 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120057
  have eq120059 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq120058
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120058
    | exact resolve eq120058 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120058
  have eq120060 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq120059
  have eq120115 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1280 y x x
       have i₂ := eq120060
       grind)
    | exact superpose eq120060 eq1280
    | exact resolve eq1280 eq120060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq120140 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op (M.op (M.op x y) X0) (M.op X0 X1)) x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq15853 y x X0 X1
       have i₂ := eq120060
       grind)
    | exact superpose eq120060 eq15853
    | exact resolve eq15853 eq120060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15853 eq120060
  have eq120211 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1841 eq120140
    | exact resolve eq120140 eq1841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841 eq120140
  have eq120220 : y = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq120115 x
       have i₂ := eq674 sF0 sF0 x
       grind)
    | exact superpose eq674 eq120115
    | exact resolve eq120115 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq120115
  have eq120527 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq234 y
       have i₂ := eq120211
       grind)
    | exact superpose eq120211 eq234
    | exact resolve eq234 eq120211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq120211
  have eq120694 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq120527
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq120527
    | exact resolve eq120527 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq120527
  have eq120712 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq120694
    | exact resolve eq120694 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120694
  have eq121788 : (σ y) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq120712 eq54
    | exact resolve eq54 eq120712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120712
  have eq123105 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op x (M.op (M.op (M.op x y) x) X0))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq120220 eq28740
    | exact resolve eq28740 eq120220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28740 eq120220
  have eq123174 : (σ (M.op x y)) = (M.op (M.op (σ (M.op (M.op x x) (M.op x y))) x) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq123105 x
       have i₂ := eq13077 x sF0 x x
       grind)
    | exact superpose eq13077 eq123105
    | exact resolve eq123105 eq13077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13077 eq123105
  have eq123214 : (σ (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) x) (M.op x y)) x) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq323 eq123174
    | exact resolve eq123174 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq123174
  have eq123227 : (σ (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) x) x) (M.op x y)) x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9546 eq123214
    | exact resolve eq123214 eq9546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9546 eq123214
  have eq123232 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15846 eq123227
    | exact resolve eq123227 eq15846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15846 eq123227
  have eq123236 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq123232
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq123232
    | exact resolve eq123232 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq123232
  have eq123238 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq123236
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq123236
    | exact resolve eq123236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123236
  have eq123240 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq123238
    | exact resolve eq123238 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123238
  have eq123265 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq123240 eq54
    | exact resolve eq54 eq123240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq123240
  have eq131205 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq123265 eq121788
    | exact resolve eq121788 eq123265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121788 eq123265
  have eq131334 : y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq131205
  have eq131413 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq131334
       grind)
    | exact superpose eq131334 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq131334
       grind)
    | exact resolve eq12 eq131334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131334
  have eq131514 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq131413
  have eq131545 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq131514
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq131514
    | exact resolve eq131514 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131514
  have eq131560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq635
       have i₂ := eq131545
       grind)
    | exact superpose eq131545 eq635
    | exact resolve eq635 eq131545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq131585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq131560
    | exact resolve eq131560 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131560
  have eq131594 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq131585
       have r₂ := eq27
       grind)
    | exact resolve eq131585 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131585
  have eq140213 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) X1) X2)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq131594 eq57937
    | exact resolve eq57937 eq131594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57937 eq131594
  have eq140223 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq15769 eq140213
    | (have j0 := eq140213 X0 (σ y) x
       grind)
    | exact resolve eq140213 eq15769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15769 eq140213
  have eq140261 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq729 eq140223
    | exact resolve eq140223 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq140223
  have eq140262 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq140261
  have eq140297 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq140262 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq140262
       grind)
    | exact resolve eq12 eq140262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140262
  have eq140396 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq140297
  have eq140423 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq64 eq140396
    | exact resolve eq140396 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq140396
  have eq140434 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq140423
    | exact resolve eq140423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140423
  have eq140437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq140434
       have i₂ := eq131545
       grind)
    | exact superpose eq131545 eq140434
    | exact resolve eq140434 eq131545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131545 eq140434
  have eq140492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq140437
  have eq140504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq140492
    | exact resolve eq140492 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140492
  have eq140512 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq140504
       have r₂ := eq27
       grind)
    | exact resolve eq140504 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140504
  have eq140516 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq140512 eq26
    | exact resolve eq26 eq140512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq140520 : y = (τ (σ x)) := by
    first
    | exact superpose eq140512 eq39
    | exact resolve eq39 eq140512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq140512
  have eq143705 : x = y := by
    first
    | exact superpose eq38 eq140520
    | exact resolve eq140520 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140520
  have eq145002 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq143705
       grind)
    | exact superpose eq143705 eq18
    | exact resolve eq18 eq143705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq143705
  have eq150131 : (M.op (τ (σ x)) (τ (σ x))) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq140516 eq235
    | exact resolve eq235 eq140516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq140516
  have eq150309 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq38 eq150131
    | exact resolve eq150131 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq150131
  have eq150340 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq150309
       have i₂ := eq145002
       grind)
    | exact superpose eq145002 eq150309
    | exact resolve eq150309 eq145002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145002 eq150309
  have eq150351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq150340 eq11
    | exact resolve eq11 eq150340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150340
  have eq150404 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq150351
    | exact resolve eq150351 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq150351
  have eq150406 : False := by grind
  exact eq150406
