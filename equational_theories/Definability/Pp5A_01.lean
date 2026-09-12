import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq76 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq85
  have eq135 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq139 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq143 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq139 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq139 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq153 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       have j1 := eq76 X1 (σ X0)
       grind)
    | (have r₁ := eq143 X0 X0
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq143 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq143
  have eq160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq153
    | (have j0 := eq153 X0 X1
       grind)
    | exact resolve eq153 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq167 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq161
    | exact resolve eq161 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq161 x y
       grind)
    | exact superpose eq161 eq16
    | exact resolve eq16 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq239 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq167 X0 (τ X1)
       grind)
    | exact superpose eq167 eq18
    | exact resolve eq18 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq167
  have eq252 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq239
    | exact resolve eq239 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq258 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq252
    | exact resolve eq252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq350 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq178
       have i₂ := eq258 x y
       grind)
    | exact superpose eq258 eq178
    | exact resolve eq178 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq258
  have eq351 : False := by grind
  exact eq351

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation1242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq432 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq432 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq445 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq450 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq439
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq439 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq457 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq445 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq445 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq445 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq445 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq460 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq450
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq450
    | exact resolve eq450 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq472 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq457 X0 (τ X1)
       grind)
    | exact superpose eq457 eq18
    | (have j1 := eq457 X0 (τ X1)
       grind)
    | exact resolve eq18 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq489 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq472 (τ X0) X1
       grind)
    | exact superpose eq472 eq17
    | (have j1 := eq472 (τ X0) X1
       grind)
    | exact resolve eq17 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq472
  have eq973 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq968 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq968
    | (have j0 := eq968 X0 X1
       grind)
    | exact resolve eq968 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq987 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq973 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq973
    | (have j0 := eq973 X0 X1
       grind)
    | exact resolve eq973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq990 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq987 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq987
    | (have j0 := eq987 X0 X1
       grind)
    | exact resolve eq987 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1054 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq990 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq990
    | (have j0 := eq990 X1 (σ X0)
       grind)
    | exact resolve eq990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1448 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1054 X0 X0
       have i₂ := eq457 X0 (σ X0)
       grind)
    | exact superpose eq457 eq1054
    | (have j0 := eq1054 X1 X0
       have j1 := eq457 X0 (σ X1)
       grind)
    | exact resolve eq1054 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq1054
  have eq1484 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1448 X0 X1
       have j1 := eq489 X0 (σ X1)
       grind)
    | (have r₁ := eq1448 X0 X1
       have r₂ := eq489 X0 (σ X1)
       grind)
    | exact resolve eq1448 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq1448
  have eq1660 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1484 (σ X0) X1
       grind)
    | exact superpose eq1484 eq28
    | (have j1 := eq1484 (σ X0) X1
       grind)
    | exact resolve eq28 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1484
  have eq1671 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1660 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1660
    | (have j0 := eq1660 X0 X1
       grind)
    | exact resolve eq1660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1685 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1671 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1671
    | (have j0 := eq1671 X0 X1
       grind)
    | exact resolve eq1671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671
  have eq1694 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1685 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1685
    | (have j0 := eq1685 X0 X1
       grind)
    | exact resolve eq1685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685
  have eq1787 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1694 x y
       grind)
    | exact superpose eq1694 eq16
    | (have j1 := eq1694 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1694 x y
       grind)
    | exact resolve eq16 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1812 : x = (k x y) := by grind
  clear eq1787
  have eq2042 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq460
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq460
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq460 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2043 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq2042
  have eq2044 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq2043
       have r₂ := eq12 x y
       grind)
    | exact resolve eq2043 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2045 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2044
       have i₂ := eq1812
       grind)
    | exact superpose eq1812 eq2044
    | exact resolve eq2044 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044
  have eq2046 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2045
       have i₂ := eq1812
       grind)
    | exact superpose eq1812 eq2045
    | exact resolve eq2045 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq2047 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq460
       have i₂ := eq2046
       grind)
    | exact superpose eq2046 eq460
    | exact resolve eq460 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq2046
  have eq2057 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2047
  have eq2058 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2057
       have i₂ := eq1812
       grind)
    | exact superpose eq1812 eq2057
    | exact resolve eq2057 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2059 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2058
  have eq2061 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq16
    | exact resolve eq16 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq2090 : (σ x) ≠ (σ x) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2061
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq2061
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq2061 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2091 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq2090
  have eq2093 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq2091
       have r₂ := eq12 x y
       grind)
    | exact resolve eq2091 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2094 : x = (M.op x y) := by
    first
    | (have i₁ := eq2093
       have i₂ := eq1812
       grind)
    | exact superpose eq1812 eq2093
    | exact resolve eq2093 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812 eq2093
  have eq2095 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2061
       have i₂ := eq2094
       grind)
    | exact superpose eq2094 eq2061
    | exact resolve eq2061 eq2094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061 eq2094
  have eq2107 : False := by grind
  exact eq2107

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_Equation1242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq30 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq33 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq33 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq38
    | (have j0 := eq38 X0 X1
       grind)
    | exact resolve eq38 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq44 X0 X1
       grind)
    | exact resolve eq45 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq45
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq88 X0 X0
       have r₂ := eq47 X0 X0
       grind)
    | exact resolve eq88 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq88
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq15
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq210
    | exact resolve eq210 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq210
  have eq219 : False := by grind
  exact eq219

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxy_x_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x y) X0) y)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X3) = (M.op (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X3) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X3) X0 X1
       have i₂ := eq14 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq61 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op (M.op X1 X2) X0) X2) X0) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X1 X2) X0) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op (M.op X1 X2) X0) X2) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X1 X2) X0) X2) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X1 X2) X0) X2) X0) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
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
  have eq76 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq172 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
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
  have eq194 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op (M.op X1 x) sF4) x)
       have i₂ := eq14 sF4 X1 x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (σ y)) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq590
    | exact resolve eq590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq594 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq591
       have r₂ := eq27
       grind)
    | exact resolve eq591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq596 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq594
    | exact resolve eq594 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq598 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq596
    | exact resolve eq596 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq600 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq598 eq77
    | (have r₁ := eq77
       have r₂ := eq598
       grind)
    | exact resolve eq77 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq603 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq598 eq27
    | exact resolve eq27 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq598
  have eq605 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq600
  have eq607 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0 X1
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) = (M.op (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) (M.op X0 (M.op (M.op (M.op X4 X5) X0) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X0 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X4 X5
       have i₂ := eq52 X1 X0 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X0 (M.op (M.op (M.op X1 X2) X0) X2) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) y) = (M.op (M.op (M.op (M.op x y) X0) y) (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op (M.op X3 X0) (M.op (M.op (M.op X4 X5) X3) X5))))) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X2 X1 X0 (M.op (M.op X3 X0) (M.op (M.op (M.op X4 X5) X3) X5))
       have i₂ := eq52 X3 X0 X4 X5
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op (M.op (M.op X3 X4) X0) X4)))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X2 X1 X0 (M.op (M.op (M.op X3 X4) X0) X4)
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op (M.op (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op (M.op X4 X5) X3) X5)) X2) (M.op (M.op X0 X1) X1))) = X2 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op (M.op X4 X5) X3) X5)) X2 X0 X1
       have i₂ := eq52 X3 (M.op X0 X1) X4 X5
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) = (M.op (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0
       have i₂ := eq52 X1 X0 X2 X3
       grind)
    | exact superpose eq52 eq13
    | (have j0 := eq13 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3)) X1
       have r₂ := eq52 X0 X1 X2 X3
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) = (M.op (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq623 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq629 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq612 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq612
    | exact resolve eq612 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq630 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = (M.op (M.op (M.op (M.op x y) X0) y) X0) := by
    intro X0
    first
    | (have i₁ := eq611 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq611
    | exact resolve eq611 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq631 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq610 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq610
    | exact resolve eq610 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq632 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) = (M.op (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq609 X0 X1 X2 X3 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq609
    | exact resolve eq609 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq647 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq605
       have r₂ := eq604
       grind)
    | exact resolve eq605 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq605
  have eq650 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq647 eq114
    | exact resolve eq114 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq647 eq82
    | exact resolve eq82 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq654 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq650
  have eq658 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq651
    | exact resolve eq651 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq659 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq654
       have r₂ := eq603
       grind)
    | exact resolve eq654 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq654
  have eq662 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq658
       have r₂ := eq76
       grind)
    | exact resolve eq658 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq672 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op (M.op X1 X2) (M.op X2 X3)) X2 X2 X3
       have i₂ := eq14 (M.op X2 X3) X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op (M.op X2 X3) X3) (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X1) (M.op (M.op (M.op X4 X5) (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X1)) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X1) (M.op (M.op X2 X3) X3) X4 X5
       have i₂ := eq53 X2 X3 X0 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op X5 X4) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X1) X5) (M.op (M.op X2 X3) X3)))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X5 X4 (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X1) (M.op (M.op X2 X3) X3)
       have i₂ := eq53 X2 X3 X0 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq692 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op (M.op X2 X3) X3) (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq688 X0 X1 X2 X3 x x
       have i₂ := eq14 (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X1) x x
       grind)
    | exact superpose eq14 eq688
    | exact resolve eq688 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq699 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq659 eq64
    | (have r₁ := eq64
       have r₂ := eq659
       grind)
    | exact resolve eq64 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq702 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq699
  have eq769 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq662
       grind)
    | exact superpose eq662 eq73
    | exact resolve eq73 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq662
  have eq774 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq769
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq769
    | exact resolve eq769 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq780 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq774 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq781 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq780
  have eq785 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq781
    | exact resolve eq781 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq788 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq785
    | exact resolve eq785 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq789 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq788
  have eq792 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq789 eq27
    | exact resolve eq27 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq843 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq702 eq114
    | exact resolve eq114 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq844 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq702 eq82
    | exact resolve eq82 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq702
  have eq846 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq843
  have eq914 : (τ (σ (M.op x y))) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq846 eq844
    | exact resolve eq844 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq929 : (τ (σ (M.op x y))) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq914
  have eq931 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq929
    | exact resolve eq929 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq929
  have eq1026 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op (M.op (M.op X0 X1) (σ x)) X1))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq659 eq608
    | exact resolve eq608 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq1058 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1026 x x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq1026
    | exact resolve eq1026 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1060 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1058 eq844
    | exact resolve eq844 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq1058
  have eq1075 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1060
  have eq1081 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1075
    | exact resolve eq1075 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1075
  have eq1085 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1081
       have r₂ := eq76
       grind)
    | exact resolve eq1081 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1081
  have eq1088 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq931
       have i₂ := eq1085
       grind)
    | exact superpose eq1085 eq931
    | exact resolve eq931 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq1085
  have eq1092 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1088
  have eq1102 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1092 eq20
    | exact resolve eq20 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1104 : ∀ X0 : G, (M.op X0 (M.op (M.op y X0) y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1092 eq50
    | exact resolve eq50 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1116 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq1127 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1102
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1102
    | exact resolve eq1102 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1133 : (k x y) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1127 eq57
    | exact resolve eq57 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1148 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1127 eq792
    | (have r₁ := eq792
       have r₂ := eq1127
       grind)
    | exact resolve eq792 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq1164 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1148
  have eq1165 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1164
  have eq1179 : (k x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61 eq1133
    | exact resolve eq1133 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1189 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op (M.op (M.op X0 X1) (σ x)) X1))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1165 eq608
    | exact resolve eq608 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1195 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1189 x x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq1189
    | exact resolve eq1189 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1210 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) := by
    intro X0
    first
    | exact superpose eq629 eq14
    | exact resolve eq14 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1278 : ∀ X0 : G, (k (M.op (M.op (M.op x y) X0) y) y) = (M.op (M.op (M.op (M.op x y) X0) y) y) := by
    intro X0
    first
    | exact superpose eq630 eq66
    | exact resolve eq66 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1311 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1127 eq1195
    | exact resolve eq1195 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq1195
  have eq1330 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1311
  have eq1388 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1330 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq1330
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1330
       grind)
    | exact resolve eq13 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1396 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1330 eq221
    | exact resolve eq221 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq1330
  have eq1399 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1388
  have eq1400 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51 eq1396
    | exact resolve eq1396 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq2967 : (k x (M.op x y)) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1399 eq61
    | exact resolve eq61 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1399
  have eq3500 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1400 eq2967
    | exact resolve eq2967 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400 eq2967
  have eq3529 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3500
  have eq3531 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq3529
    | exact resolve eq3529 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3529
  have eq3536 : x = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3531 eq1179
    | exact resolve eq1179 eq3531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq3531
  have eq3542 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq3536
  have eq3596 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq631
    | exact resolve eq631 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3597 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq629 eq631
    | exact resolve eq631 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq3598 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = (M.op (M.op (M.op (M.op x y) X0) y) y) := by
    intro X0
    first
    | exact superpose eq630 eq631
    | exact resolve eq631 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq3602 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X1) X2
       have i₂ := eq631 X2 X0 X1
       grind)
    | exact superpose eq631 eq14
    | exact resolve eq14 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3604 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 x) X1) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq607 (M.op X0 x) X1
       have i₂ := eq631 X1 X0 x
       grind)
    | exact superpose eq631 eq607
    | exact resolve eq607 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq631
  have eq3682 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq3542
       grind)
    | exact superpose eq3542 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq3542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3542
  have eq3683 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq3682
  have eq4114 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X2) (M.op (M.op X4 X3) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) X4) (M.op (M.op (σ x) (σ y)) (σ y)))))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq217 eq616
    | exact resolve eq616 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq4136 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (σ y) X2) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X3 X4) (σ x)) X4)))))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq608 eq616
    | exact resolve eq616 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4172 : ∀ X0 X1 X2 X3 X4 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op X3 X4) X2) X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq608 X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op X3 X4) X2) X4)))
       have i₂ := eq616 X2 X0 X1 X3 X4
       grind)
    | exact superpose eq616 eq608
    | exact resolve eq608 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq616
  have eq7024 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X1) X1 x x
       have i₂ := eq692 x x X0 X1
       grind)
    | exact superpose eq692 eq52
    | exact resolve eq52 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq7930 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq172 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq8100 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq9347 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X2) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) (σ y)))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq219 eq615
    | exact resolve eq615 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq9348 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op (M.op x y) y) X2) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (σ y)) (σ y)))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq223 eq615
    | exact resolve eq615 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq11787 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (σ y)) (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (σ y))) X2)) X0) (M.op (M.op (M.op x y) y) y))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq223 eq619
    | exact resolve eq619 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq12184 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (σ y)) X0) (M.op (M.op (M.op x y) y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11787 X0 x x
       have i₂ := eq14 (M.op (M.op sF4 sF0) sF3) x x
       grind)
    | exact superpose eq14 eq11787
    | exact resolve eq11787 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11787
  have eq12934 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (σ y)) (σ y)) X1) (M.op (M.op (M.op x y) y) y)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq223 eq689
    | exact resolve eq689 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq689
  have eq14860 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) = (k (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq628 X0 X1 X2 X3
       have i₂ := eq632 X0 X1 X2 X3
       grind)
    | exact superpose eq632 eq628
    | exact resolve eq628 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq632
  have eq15171 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14860 X1 (M.op X0 X1) (M.op x (M.op X0 X1)) (M.op X0 X1)
       have i₂ := eq672 X0 X1 x (M.op X0 X1)
       grind)
    | exact superpose eq672 eq14860
    | exact resolve eq14860 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq14860
  have eq114008 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = (k (M.op (M.op (M.op x y) X0) y) y) := by
    intro X0
    first
    | exact superpose eq3598 eq1278
    | exact resolve eq1278 eq3598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278 eq3598
  have eq857372 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (σ y)) X1) (M.op (M.op (M.op x y) y) y)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq3597 eq12934
    | exact resolve eq12934 eq3597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12934
  have eq1047515 : x = (M.op x (M.op y (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (σ y)) y) (M.op (M.op (M.op x y) y) y)))) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq857372 x y
       have i₂ := eq3683
       grind)
    | exact superpose eq3683 eq857372
    | exact resolve eq857372 eq3683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3683 eq857372
  have eq1047528 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12184 eq1047515
    | exact resolve eq1047515 eq12184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12184 eq1047515
  have eq1047714 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1047528
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1047528
    | exact resolve eq1047528 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047528
  have eq1047715 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1047714
  have eq1047870 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1104 x
       have i₂ := eq1047715
       grind)
    | exact superpose eq1047715 eq1104
    | exact resolve eq1104 eq1047715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq1047715
  have eq1048299 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1047870
  have eq1048327 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1048299
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1048299
    | exact resolve eq1048299 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048299
  have eq1090268 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1092 eq1048327
    | exact resolve eq1048327 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq1048327
  have eq1090922 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1090268
       have r₂ := eq1116
       grind)
    | exact resolve eq1090268 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq1090268
  have eq1090930 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1090922
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1090922
    | exact resolve eq1090922 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090922
  have eq1090931 : x = (M.op x y) := by grind
  clear eq1090930
  have eq1090933 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1090931 eq20
    | exact resolve eq20 eq1090931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1091596 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1090933
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1090933
    | exact resolve eq1090933 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090933
  have eq1091745 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1091596 eq26
    | exact resolve eq26 eq1091596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095499 : ∀ X0 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op X0 x) x))) := by
    intro X0
    first
    | exact superpose eq4114 eq3604
    | exact resolve eq3604 eq4114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3604
  have eq1095767 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq4114 eq114008
    | exact resolve eq114008 eq4114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114 eq114008
  have eq1095969 : (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq1090931 eq1095767
    | exact resolve eq1095767 eq1090931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095767
  have eq1096155 : ∀ X0 : G, y = (M.op y (M.op x (M.op (M.op X0 x) x))) := by
    intro X0
    first
    | exact superpose eq1090931 eq1095499
    | exact resolve eq1095499 eq1090931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095499
  have eq1097769 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq1095969
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1095969
    | exact resolve eq1095969 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095969
  have eq1097892 : y = (M.op y x) := by
    first
    | (have i₁ := eq1096155 x
       have i₂ := eq7024 x x
       grind)
    | exact superpose eq7024 eq1096155
    | exact resolve eq1096155 eq7024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7024 eq1096155
  have eq1098657 : x = (k x y) := by
    first
    | exact superpose eq1090931 eq1097769
    | exact resolve eq1097769 eq1090931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097769
  have eq1099965 : (M.op y x) = (k (M.op y x) x) := by
    first
    | (have i₁ := eq15171 y x
       have i₂ := eq1097892
       grind)
    | exact superpose eq1097892 eq15171
    | exact resolve eq15171 eq1097892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15171
  have eq1100035 : y = (k y x) := by
    first
    | (have i₁ := eq1099965
       have i₂ := eq1097892
       grind)
    | exact superpose eq1097892 eq1099965
    | exact resolve eq1099965 eq1097892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097892 eq1099965
  have eq1100731 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8100 x
       have i₂ := eq1098657
       grind)
    | exact superpose eq1098657 eq8100
    | (have j0 := eq8100 x
       grind)
    | exact resolve eq8100 eq1098657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8100 eq1098657
  have eq1100750 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1100731
  have eq1100765 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1100750
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1100750
    | exact resolve eq1100750 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100750
  have eq1100793 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1091596 eq1100765
    | exact resolve eq1100765 eq1091596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100765
  have eq1100821 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1100793
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1100793
    | exact resolve eq1100793 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1100793
  have eq1100848 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1091596 eq1100821
    | exact resolve eq1100821 eq1091596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100821
  have eq1106149 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (σ y) X2) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X3 X4) (σ (M.op x y))) X4)))))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1091596 eq4136
    | exact resolve eq4136 eq1091596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq1106187 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7930 y
       have i₂ := eq1100035
       grind)
    | exact superpose eq1100035 eq7930
    | (have j0 := eq7930 y
       grind)
    | exact resolve eq7930 eq1100035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7930 eq1100035
  have eq1106206 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1106187
  have eq1106226 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1106206
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1106206
    | exact resolve eq1106206 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106206
  have eq1106258 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1106226
    | exact resolve eq1106226 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106226
  have eq1106290 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1106258
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1106258
    | exact resolve eq1106258 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1106258
  have eq1106312 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1106290
    | exact resolve eq1106290 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1106290
  have eq1106329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1091596 eq1106312
    | exact resolve eq1106312 eq1091596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106312
  have eq1106346 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1106329
       have r₂ := eq27
       grind)
    | exact resolve eq1106329 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106329
  have eq1106388 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1106346 eq27
    | exact resolve eq27 eq1106346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1107463 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (σ y) X2) (M.op (σ y) (M.op (M.op (M.op X3 X4) (σ (M.op x y))) X4)))))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1106346 eq1106149
    | exact resolve eq1106149 eq1106346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106149
  have eq1110090 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (σ y) X2) (M.op (σ y) (M.op (M.op (M.op X3 X4) (σ (M.op x y))) X4)))))) = (M.op (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (σ y) X2) (M.op (σ y) (M.op (M.op (M.op X3 X4) (σ (M.op x y))) X4)))))) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1107463 eq3596
    | exact resolve eq3596 eq1107463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596
  have eq1111406 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (σ y) X2) (M.op (σ y) (M.op (M.op (M.op X3 X4) (σ (M.op x y))) X4)))))) = (M.op (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (σ y) X2) (M.op (σ y) (M.op (M.op (M.op X3 X4) (σ (M.op x y))) X4)))))) (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1106346 eq1110090
    | exact resolve eq1110090 eq1106346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110090
  have eq1113018 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) X0) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq1107463 eq1111406
    | exact resolve eq1111406 eq1107463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107463 eq1111406
  have eq1114716 : ∀ X0 X1 X2 X3 X4 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ (M.op x y))) (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op X3 X4) X2) X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1091596 eq4172
    | exact resolve eq4172 eq1091596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172 eq1091596
  have eq1114717 : ∀ X0 X1 X2 X3 X4 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op X0 (σ (M.op x y))) (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op X3 X4) X2) X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1106346 eq1114716
    | exact resolve eq1114716 eq1106346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114716
  have eq1115303 : ∀ X0 X1 X2 X3 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (σ (M.op x y))) (M.op (σ y) (M.op (M.op X1 (σ y)) (M.op (M.op (M.op X2 X3) X1) X3)))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1210 eq1114717
    | exact resolve eq1114717 eq1210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210 eq1114717
  have eq1119041 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (σ (M.op x y))) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1115303 X0 X0 x x
       have i₂ := eq52 X0 sF3 x x
       grind)
    | exact superpose eq52 eq1115303
    | exact resolve eq1115303 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1115303
  have eq1120191 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1119041 x
       have i₂ := eq3602 (M.op sF4 x) sF3 sF1
       grind)
    | exact superpose eq3602 eq1119041
    | exact resolve eq1119041 eq3602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3602 eq1119041
  have eq1139378 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1106346 eq1091745
    | exact resolve eq1091745 eq1106346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091745
  have eq1295224 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X2) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq3597 eq9347
    | exact resolve eq9347 eq3597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9347
  have eq1295225 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op (σ y) (σ y)) X2) (M.op (M.op (σ y) (σ y)) (σ y)))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq1106346 eq1295224
    | exact resolve eq1295224 eq1106346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295224
  have eq1295226 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (σ y) X2) (M.op (σ y) (σ y)))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq1120191 eq1295225
    | exact resolve eq1295225 eq1120191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295225
  have eq1295227 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (σ y) X2) (σ y))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq1120191 eq1295226
    | exact resolve eq1295226 eq1120191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120191 eq1295226
  have eq1302200 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op (M.op x y) y) X2) (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (σ y)))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq3597 eq9348
    | exact resolve eq9348 eq3597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3597 eq9348
  have eq1302201 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op x y) X2) (M.op (M.op (M.op (σ x) (σ y)) x) (σ y)))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq1090931 eq1302200
    | exact resolve eq1302200 eq1090931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302200
  have eq1302202 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op x y) X2) (M.op (M.op (σ y) x) (σ y)))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq1106346 eq1302201
    | exact resolve eq1302201 eq1106346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106346 eq1302201
  have eq1302203 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op (M.op x y) X2) (M.op (M.op (σ y) x) (σ y)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1302202 X0 X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1302202
    | (have j0 := eq1302202 X0 X1 X2
       grind)
    | exact resolve eq1302202 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1302202
  have eq1302204 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op x X2) (M.op (M.op (σ y) x) (σ y)))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq1090931 eq1302203
    | exact resolve eq1302203 eq1090931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090931 eq1302203
  have eq1356242 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op (M.op x X0) (M.op (M.op (σ y) x) (σ y)))))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1100848 eq1302204
    | exact resolve eq1302204 eq1100848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100848 eq1302204
  have eq1356260 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1295227 eq1356242
    | exact resolve eq1356242 eq1295227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295227 eq1356242
  have eq1356625 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1139378 eq1356260
    | exact resolve eq1356260 eq1139378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356260
  have eq1356860 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1356625
       have r₂ := eq1106388
       grind)
    | exact resolve eq1356625 eq1106388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356625
  have eq1357237 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq1356860 eq1113018
    | exact resolve eq1113018 eq1356860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113018 eq1356860
  have eq1358035 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1139378 eq1357237
    | exact resolve eq1357237 eq1139378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357237
  have eq1358244 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1139378 eq1358035
    | exact resolve eq1358035 eq1139378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139378 eq1358035
  have eq1358408 : False := by grind
  exact eq1358408

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation1445 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1445 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq566 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 y x
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : (k x x) ≠ (k y y) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq566
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq566
    | exact resolve eq566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq1226 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 x y
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1236 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq1226
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1226
    | exact resolve eq1226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1244 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1236
       have i₂ := eq21 (σ x) (σ y)
       grind)
    | exact superpose eq21 eq1236
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1236
       have r₂ := eq21 (σ x) (σ y)
       grind)
    | (have r₁ := eq1236
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1236
       have r₂ := eq21 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1236 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1236
  have eq1246 : x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1244
  have eq1322 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1246
       grind)
    | exact superpose eq1246 eq9
    | exact resolve eq9 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1323 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1322
  have eq1324 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1323
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1323
    | exact resolve eq1323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1325 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1324
  have eq1326 : (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1325
  have eq1404 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1326
       grind)
    | exact superpose eq1326 eq10
    | exact resolve eq10 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1406 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1404
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1404
    | exact resolve eq1404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1407 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1406
  have eq1411 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1407
       grind)
    | exact superpose eq1407 eq22
    | exact resolve eq22 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1458 : (k x x) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1411
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1411
    | exact resolve eq1411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1411
  have eq1480 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq573
       have i₂ := eq1458
       grind)
    | exact superpose eq1458 eq573
    | (have r₁ := eq573
       have r₂ := eq1458
       grind)
    | exact resolve eq573 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq1458
  have eq1483 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1480
  have eq1487 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1483
       have i₂ := eq20 (σ y) (σ x)
       grind)
    | exact superpose eq20 eq1483
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1483
       have r₂ := eq20 (σ y) (σ x)
       grind)
    | (have r₁ := eq1483
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1483
       have r₂ := eq20 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1483 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1483
  have eq1488 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1487
  have eq1489 : x = y ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1488
  have eq1491 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1489
       have r₂ := eq1407
       grind)
    | exact resolve eq1489 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407 eq1489
  have eq1492 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1491
       grind)
    | exact superpose eq1491 eq9
    | exact resolve eq9 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1493 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1492
  have eq1494 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1493
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1493
    | exact resolve eq1493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1495 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1494
  have eq1496 : (σ x) = (σ y) := by grind
  clear eq1495
  have eq1498 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq15
    | exact resolve eq15 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1545 : x = y := by
    first
    | (have i₁ := eq1498
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1498
    | exact resolve eq1498 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1548 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1545
       grind)
    | exact superpose eq1545 eq9
    | exact resolve eq9 eq1545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq1549 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1548
  have eq1550 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1549
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1549
    | exact resolve eq1549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1551 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1550
  have eq1552 : False := by grind
  exact eq1552

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq121 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq57 (τ X0)
       grind)
    | exact superpose eq57 eq36
    | (have j1 := eq57 (τ X0)
       grind)
    | exact resolve eq36 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq259 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq86 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq269 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq270 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq275 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq276 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq888 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq276
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq276 x y
       grind)
    | exact superpose eq276 eq16
    | (have j1 := eq276 x y
       grind)
    | exact resolve eq16 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq923 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq888
    | (have j0 := eq888 X0 X1
       grind)
    | exact resolve eq888 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq888
  have eq925 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq923 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq923
    | exact resolve eq923 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq939 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq923 X1 X0
       grind)
    | exact superpose eq923 eq32
    | (have j1 := eq923 X1 X0
       grind)
    | exact resolve eq32 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq923
  have eq984 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq925 (τ X0) X1
       grind)
    | exact superpose eq925 eq18
    | (have j1 := eq925 (τ X0) X1
       grind)
    | exact resolve eq18 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq925
  have eq1351 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq984 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq984
    | exact resolve eq984 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1400 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1351 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1351
    | (have j0 := eq1351 X0 X1
       grind)
    | exact resolve eq1351 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq1532 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq896
       have i₂ := eq1400 x y
       grind)
    | exact superpose eq1400 eq896
    | (have j1 := eq1400 (σ x) (σ y)
       grind)
    | (have r₁ := eq896
       have r₂ := eq1400 x y
       grind)
    | exact resolve eq896 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq1400
  have eq1533 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq1532
  have eq1540 : (k y (τ (σ y))) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq939 y (σ y)
       have i₂ := eq1533
       grind)
    | exact superpose eq1533 eq939
    | exact resolve eq939 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939 eq1533
  have eq1572 : x = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1540
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1540
    | exact resolve eq1540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq1573 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1572
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1572
    | exact resolve eq1572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq9209 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq121
  have eq9263 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9209 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq9209
    | (have j0 := eq9209 X0
       grind)
    | exact resolve eq9209 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq9209
  have eq9264 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq9263 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9263
  have eq9274 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9264 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9264
    | exact resolve eq9264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9264
  have eq9352 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq9274 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq9274
    | exact resolve eq9274 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9274
  have eq9357 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9352 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9352
    | exact resolve eq9352 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9352
  have eq9646 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq9357 (σ X0)
       grind)
    | exact superpose eq9357 eq15
    | exact resolve eq15 eq9357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9657 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1573
       have i₂ := eq9357 y
       grind)
    | exact superpose eq9357 eq1573
    | exact resolve eq1573 eq9357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq9658 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq9657
  have eq9669 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9646 X0
       have i₂ := eq9357 X0
       grind)
    | exact superpose eq9357 eq9646
    | exact resolve eq9646 eq9357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9357 eq9646
  have eq9783 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq9838 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9783 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq9783
    | exact resolve eq9783 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9783
  have eq9853 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq9838
  have eq10144 : y = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9658
       grind)
    | exact superpose eq9658 eq10
    | exact resolve eq10 eq9658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9658
  have eq10262 : x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10144
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10144
    | exact resolve eq10144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10144
  have eq10276 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10262
       grind)
    | exact superpose eq10262 eq16
    | exact resolve eq16 eq10262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10262
  have eq10339 : x = (M.op y y) := by
    first
    | (have r₁ := eq10276
       have r₂ := eq9669 x
       grind)
    | exact resolve eq10276 eq9669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9669 eq10276
  have eq21576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9853 y
       have i₂ := eq10339
       grind)
    | exact superpose eq10339 eq9853
    | exact resolve eq9853 eq10339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9853 eq10339
  have eq21746 : False := by grind
  exact eq21746

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyy_pxy_pyx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X2 X1))) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq113 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq113 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq113 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq129 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X2 X1))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq100 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq100 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have r₂ := eq12 (M.op X2 (M.op X2 (M.op (M.op X0 X0) (M.op X0 X0)))) (M.op X0 X0)
       grind)
    | (have r₁ := eq100 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq100 X0 X0 X2
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq100 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq185 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq903 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq185 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq185 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq185 eq9
    | exact resolve eq9 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1411 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq903 X0 x X1
       grind)
    | exact superpose eq903 eq9
    | exact resolve eq9 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq1506 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1411 X1 X1 (M.op x (M.op x X0))
       have i₂ := eq129 X1 X0 x
       grind)
    | exact superpose eq129 eq1411
    | (have j1 := eq129 X1 X0 x
       grind)
    | exact resolve eq1411 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1411
  have eq1561 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1506 X0 X1
       have j1 := eq116 X0 X1
       grind)
    | (have r₁ := eq1506 X0 X1
       have r₂ := eq116 X0 X1
       grind)
    | (have r₁ := eq1506 X0 X0
       have r₂ := eq116 X0 X0
       grind)
    | exact resolve eq1506 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1506
  have eq1574 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1561 (σ X1) (σ X0)
       grind)
    | exact superpose eq1561 eq15
    | exact resolve eq15 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1593 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1574 X0 X1
       have i₂ := eq1561 X1 X0
       grind)
    | exact superpose eq1561 eq1574
    | exact resolve eq1574 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561 eq1574
  have eq1954 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1593 x y
       grind)
    | exact superpose eq1593 eq16
    | (have r₁ := eq16
       have r₂ := eq1593 x y
       grind)
    | exact resolve eq16 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1999 : False := by grind
  exact eq1999

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pxx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ X0) (σ X1)
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq92 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq212 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ X0) (σ X1)) (M.op X2 (M.op X2 (σ X1)))) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq69 X1 X0
       grind)
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq9
    | (have j1 := eq69 X1 X0
       grind)
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq229 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq243 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq239
    | (have j0 := eq239 X0 X1
       grind)
    | exact resolve eq239 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq245 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq227 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq227
    | (have j0 := eq227 X0 X1
       grind)
    | exact resolve eq227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq246 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq245 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq252 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq246 X1 X0
       have j1 := eq243 X1 X0
       grind)
    | (have r₁ := eq246 X0 X1
       have r₂ := eq243 X0 X1
       grind)
    | exact resolve eq246 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq246
  have eq438 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X2 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq572 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq438 X0 x X1
       grind)
    | exact superpose eq438 eq9
    | exact resolve eq9 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq1087 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq252 (τ X0) (τ X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq252
    | exact resolve eq252 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1205 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq252 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq1206 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1227 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1087 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1087
    | (have j0 := eq1087 X0 X1
       grind)
    | exact resolve eq1087 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1237 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1227 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1227
    | (have j0 := eq1227 X0 X1
       grind)
    | exact resolve eq1227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1239 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1237 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1237
    | (have j0 := eq1237 X0 X1
       grind)
    | exact resolve eq1237 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1240 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1239 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1239
    | (have j0 := eq1239 X0 X1
       grind)
    | exact resolve eq1239 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1241 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1240 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1240
    | (have j0 := eq1240 X0 X1
       grind)
    | exact resolve eq1240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1242 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1206 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1206
    | exact resolve eq1206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1284 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1242 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1242
    | exact resolve eq1242 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1242
  have eq1286 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1284 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1284
    | exact resolve eq1284 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1774 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq572 (σ X0) (σ X1) (M.op x (M.op x (σ X0)))
       have i₂ := eq212 X1 X0 x
       grind)
    | exact superpose eq212 eq572
    | (have j1 := eq212 X1 X0 x
       grind)
    | exact resolve eq572 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq572
  have eq1827 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1774 X0 X1
       have i₂ := eq1206 X0
       grind)
    | exact superpose eq1206 eq1774
    | (have j0 := eq1774 X0 X1
       grind)
    | exact resolve eq1774 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774
  have eq1844 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1827 X0 X1
       have i₂ := eq1286 X0
       grind)
    | exact superpose eq1286 eq1827
    | (have j0 := eq1827 X0 X1
       grind)
    | exact resolve eq1827 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827
  have eq2137 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1241 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq2862 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2137 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq2137 (σ X1) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq2137
    | (have j1 := eq69 X1 X0
       grind)
    | (have r₁ := eq2137 (σ X1) (σ X1)
       have r₂ := eq69 X1 X1
       grind)
    | (have r₁ := eq2137 (σ X0) (σ X0)
       have r₂ := eq69 X0 X0
       grind)
    | exact resolve eq2137 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2137
  have eq2889 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (k X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2862 X0 X1
       have i₂ := eq1206 X1
       grind)
    | exact superpose eq1206 eq2862
    | (have j0 := eq2862 X0 X1
       grind)
    | exact resolve eq2862 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206 eq2862
  have eq2896 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2889 X0 X1
       have i₂ := eq1286 X1
       grind)
    | exact superpose eq1286 eq2889
    | (have j0 := eq2889 X0 X1
       grind)
    | exact resolve eq2889 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286 eq2889
  have eq2900 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2896 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2896
    | (have j0 := eq2896 X0 X1
       grind)
    | exact resolve eq2896 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2896
  have eq2903 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2900 X0 X1
       have j1 := eq1844 X1 X0
       grind)
    | (have r₁ := eq2900 X1 X0
       have r₂ := eq1844 X0 X1
       grind)
    | exact resolve eq2900 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844 eq2900
  have eq2905 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2903 X0 X1
       have j1 := eq238 X1 X0
       grind)
    | (have r₁ := eq2903 X1 X0
       have r₂ := eq238 X0 X1
       grind)
    | (have r₁ := eq2903 X1 X1
       have r₂ := eq238 X1 X1
       grind)
    | exact resolve eq2903 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq2903
  have eq2907 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2905 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2905
    | exact resolve eq2905 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2927 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2905 y x
       grind)
    | exact superpose eq2905 eq16
    | exact resolve eq16 eq2905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2905
  have eq3185 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq2907 X0 (τ X1)
       grind)
    | exact superpose eq2907 eq18
    | exact resolve eq18 eq2907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2907
  have eq3243 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3185 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3185
    | exact resolve eq3185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185
  have eq3255 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3243 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3243
    | exact resolve eq3243 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243
  have eq3407 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2927
       have i₂ := eq3255 x y
       grind)
    | exact superpose eq3255 eq2927
    | exact resolve eq2927 eq3255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927 eq3255
  have eq3408 : False := by grind
  exact eq3408
