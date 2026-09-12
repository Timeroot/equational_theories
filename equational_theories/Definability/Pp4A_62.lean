import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq79 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
    | (have j1 := eq14 (σ X1) (σ X0)
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
  have eq190 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
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
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq193 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq197 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq193 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq193 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq209 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq79 X1 (σ X0)
       grind)
    | (have r₁ := eq197 X0 X0
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq197 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq197
  have eq217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq209
    | (have j0 := eq209 X0 X1
       grind)
    | exact resolve eq209 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq218 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq217 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq224 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq218
    | exact resolve eq218 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq218 x y
       grind)
    | exact superpose eq218 eq16
    | exact resolve eq16 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq317 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq224 X0 (τ X1)
       grind)
    | exact superpose eq224 eq18
    | exact resolve eq18 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq224
  have eq338 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq317 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq317
    | exact resolve eq317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq348 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq338
    | exact resolve eq338 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq375 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq235
       have i₂ := eq348 x y
       grind)
    | exact superpose eq348 eq235
    | exact resolve eq235 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq348
  have eq376 : False := by grind
  exact eq376

/-- `Equation653`: `x = x ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law653.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  clear eq37
  have eq75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq77 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq108
    | exact resolve eq108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq549 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq8584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq8584
    | exact resolve eq8584 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8584
  have eq8596 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8585
       have r₂ := eq29
       grind)
    | exact resolve eq8585 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8585
  have eq8698 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq8596
  have eq8726 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq8698
    | exact resolve eq8698 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8698
  have eq8732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq8726 eq109
    | exact resolve eq109 eq8726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq8726
  have eq8741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq8732
  have eq8744 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8741
       have r₂ := eq29
       grind)
    | exact resolve eq8741 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8741
  have eq8878 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8744
  have eq8907 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8878
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq8878
    | exact resolve eq8878 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8878
  have eq8910 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq8907
       grind)
    | exact superpose eq8907 eq46
    | exact resolve eq46 eq8907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq8907
  have eq8926 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq8910
    | exact resolve eq8910 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8910
  have eq9183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8926 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq8926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq9183
  have eq9188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq9184
    | exact resolve eq9184 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9184
  have eq9199 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq9188
       have r₂ := eq29
       grind)
    | exact resolve eq9188 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9188
  have eq9368 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9199
  have eq9399 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq9368
    | exact resolve eq9368 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9368
  have eq9413 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9399 eq8926
    | exact resolve eq8926 eq9399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8926 eq9399
  have eq9416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq9413
  have eq9421 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq9416
       have r₂ := eq29
       grind)
    | exact resolve eq9416 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9416
  have eq9576 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq9421 eq31
    | exact resolve eq31 eq9421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9421
  have eq9706 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq9576
    | exact resolve eq9576 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9576
  have eq9707 : x = y := by grind
  clear eq9706
  have eq9708 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq9707
       grind)
    | exact superpose eq9707 eq20
    | exact resolve eq20 eq9707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq9709 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq9707
       grind)
    | exact superpose eq9707 eq26
    | exact resolve eq26 eq9707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9707
  have eq9829 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq9709
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9709
    | exact resolve eq9709 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9709
  have eq9830 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9829 eq28
    | exact resolve eq28 eq9829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9829
  have eq9967 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq9708
       grind)
    | exact superpose eq9708 eq77
    | exact resolve eq77 eq9708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq9968 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  have eq10016 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq9967
    | exact resolve eq9967 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9967
  have eq10017 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq10519 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq10520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9830 eq10519
    | exact resolve eq10519 eq9830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10519
  have eq10533 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10520
       have r₂ := eq29
       grind)
    | exact resolve eq10520 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10520
  have eq10538 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9830 eq10533
    | exact resolve eq10533 eq9830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10533
  have eq10561 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10538 eq10017
    | exact resolve eq10017 eq10538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10017 eq10538
  have eq10562 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9830 eq10561
    | exact resolve eq10561 eq9830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10561
  have eq11094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10562 eq10016
    | exact resolve eq10016 eq10562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10016 eq10562
  have eq11100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11094
  have eq11104 : x = (M.op x y) := by
    first
    | (have r₁ := eq11100
       have r₂ := eq29
       grind)
    | exact resolve eq11100 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11100
  have eq11115 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq11104 eq22
    | exact resolve eq22 eq11104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq11184 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq11104 eq9968
    | exact resolve eq9968 eq11104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9968
  have eq11187 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq11184
       have i₂ := eq9708
       grind)
    | exact superpose eq9708 eq11184
    | exact resolve eq11184 eq9708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9708 eq11184
  have eq11256 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11115
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11115
    | exact resolve eq11115 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11115
  have eq11258 : x = (k x x) := by
    first
    | exact superpose eq11104 eq11187
    | exact resolve eq11187 eq11104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11104 eq11187
  have eq12404 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq549 x
       have i₂ := eq11258
       grind)
    | exact superpose eq11258 eq549
    | (have j0 := eq549 x
       grind)
    | exact resolve eq549 eq11258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq11258
  have eq12407 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12404
  have eq12413 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12407
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12407
    | exact resolve eq12407 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq12407
  have eq12424 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9830 eq12413
    | exact resolve eq12413 eq9830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9830 eq12413
  have eq12433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11256 eq12424
    | exact resolve eq12424 eq11256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11256 eq12424
  have eq12441 : False := by grind
  exact eq12441

/-- `Equation690`: `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_y_pyx_Equation690 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X1) X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op X0 (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
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
  have eq63 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq132 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq211 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op x y)) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op X1 (M.op x y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X0 (M.op (M.op x sF0) X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X0)) (M.op X1 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 (M.op (M.op x sF4) X0))
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq854 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq848 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq855 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq849 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq849 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq849 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq849 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq854 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq854 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq854 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq854 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq865 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq866 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq856 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq856
    | (have j0 := eq856 X0 X1
       grind)
    | exact resolve eq856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq1022 : y = (M.op (M.op x (M.op (M.op x y) x)) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq214 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq214
    | (have j0 := eq214 x y
       grind)
    | exact resolve eq214 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1024 : (σ y) = (M.op (M.op (σ x) (M.op (M.op x y) (σ x))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq214
    | (have j0 := eq214 (σ x) (σ y)
       grind)
    | exact resolve eq214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1048 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1022 eq14
    | exact resolve eq14 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1059 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1024 eq14
    | exact resolve eq14 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq3743 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) y) (M.op y (M.op (M.op X0 (M.op x y)) y))) := by
    intro X0
    first
    | exact superpose eq211 eq14
    | exact resolve eq14 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq3875 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) := by
    intro X0
    first
    | exact superpose eq215 eq14
    | exact resolve eq14 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq14225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq14225
    | exact resolve eq14225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14225
  have eq14237 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq14226
       have r₂ := eq27
       grind)
    | exact resolve eq14226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14226
  have eq14239 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq14237
    | exact resolve eq14237 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14237
  have eq14636 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14239 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14239
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14239
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14239
       grind)
    | exact resolve eq12 eq14239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14239
  have eq14667 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq14636
  have eq14679 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq14667
    | exact resolve eq14667 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14667
  have eq14680 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq14679
  have eq15091 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14680 eq82
    | exact resolve eq82 eq14680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15092 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14680 eq115
    | exact resolve eq115 eq14680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14680
  have eq15109 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15092
  have eq15118 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq28 eq15091
    | exact resolve eq15091 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15091
  have eq15123 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq15109
       grind)
    | exact superpose eq15109 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15109
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15109
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15109
       grind)
    | exact resolve eq12 eq15109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15124 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq15109
       grind)
    | exact superpose eq15109 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15109
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15109
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15109
       grind)
    | exact resolve eq13 eq15109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15109
  have eq15153 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15124
  have eq15154 : x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15123
  have eq15165 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15153
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15153
    | exact resolve eq15153 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15153
  have eq15166 : x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15154
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15154
    | exact resolve eq15154 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15154
  have eq15167 : x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15166
  have eq15565 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq15165
       grind)
    | exact superpose eq15165 eq44
    | exact resolve eq44 eq15165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15165
  have eq15589 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15565
    | exact resolve eq15565 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15565
  have eq15642 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq852 x y
       have i₂ := eq15167
       grind)
    | exact superpose eq15167 eq852
    | (have j0 := eq852 x y
       grind)
    | exact resolve eq852 eq15167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15167
  have eq15647 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15642
  have eq15651 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15647
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15647
    | exact resolve eq15647 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15647
  have eq15663 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15651
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15651
    | exact resolve eq15651 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15651
  have eq15670 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15663
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15663
    | exact resolve eq15663 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15663
  have eq15675 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15670
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15670
    | exact resolve eq15670 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15670
  have eq15680 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15675
    | exact resolve eq15675 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15675
  have eq15681 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq15680
  have eq15916 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15681 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15681
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15681
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15681
       grind)
    | exact resolve eq13 eq15681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15681
  have eq15946 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq15916
  have eq15958 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq15946
    | exact resolve eq15946 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15946
  have eq16203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15958 eq15589
    | exact resolve eq15589 eq15958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15589 eq15958
  have eq16210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16203
  have eq16212 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16210
       have r₂ := eq27
       grind)
    | exact resolve eq16210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16210
  have eq16599 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16212 eq64
    | (have r₁ := eq64
       have r₂ := eq16212
       grind)
    | exact resolve eq64 eq16212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16212
  have eq16620 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq16599
  have eq16627 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16620 eq82
    | exact resolve eq82 eq16620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq16620
  have eq17712 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq15118
       grind)
    | exact superpose eq15118 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15118
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15118
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15118
       grind)
    | exact resolve eq12 eq15118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15118
  have eq17747 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17712
  have eq17748 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17747
  have eq17760 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17748
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17748
    | exact resolve eq17748 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17748
  have eq17761 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17760
  have eq18096 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq17761
       grind)
    | exact superpose eq17761 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq17761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18100 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq852 x y
       have i₂ := eq17761
       grind)
    | exact superpose eq17761 eq852
    | (have j0 := eq852 x y
       grind)
    | exact resolve eq852 eq17761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18102 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq866 y x
       have i₂ := eq17761
       grind)
    | exact superpose eq17761 eq866
    | (have j0 := eq866 y x
       grind)
    | exact resolve eq866 eq17761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq17761
  have eq18103 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18102
  have eq18105 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18100
  have eq18106 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18096
  have eq18108 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18103
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq18103
    | exact resolve eq18103 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18103
  have eq18110 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18105
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18105
    | exact resolve eq18105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18105
  have eq18114 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18106
    | exact resolve eq18106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18106
  have eq18115 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18114
  have eq18125 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18108
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18108
    | exact resolve eq18108 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18108
  have eq18127 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18110
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18110
    | exact resolve eq18110 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18110
  have eq18133 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18125
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18125
    | exact resolve eq18125 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18125
  have eq18135 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18127
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18127
    | exact resolve eq18127 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18127
  have eq18139 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18133
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18133
    | exact resolve eq18133 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18133
  have eq18141 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18135
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18135
    | exact resolve eq18135 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18135
  have eq18145 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18139
       have r₂ := eq76
       grind)
    | exact resolve eq18139 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq18139
  have eq18146 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18141
    | exact resolve eq18141 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18141
  have eq18147 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18146
  have eq18163 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18115
       grind)
    | exact superpose eq18115 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18115
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18115
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18115
       grind)
    | exact resolve eq13 eq18115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18115
  have eq18197 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18163
  have eq18209 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18197
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18197
    | exact resolve eq18197 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18197
  have eq18562 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18147 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18147
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18147
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18147
       grind)
    | exact resolve eq13 eq18147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18147
  have eq18597 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18562
  have eq18611 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18597
    | exact resolve eq18597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18597
  have eq18615 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq18209
       grind)
    | exact superpose eq18209 eq44
    | exact resolve eq44 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18209
  have eq18641 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18615
    | exact resolve eq18615 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18615
  have eq19065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18641 eq18611
    | exact resolve eq18611 eq18641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18611 eq18641
  have eq19073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19065
  have eq19079 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19073
       have r₂ := eq27
       grind)
    | exact resolve eq19073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19073
  have eq19090 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19079 eq27
    | exact resolve eq27 eq19079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19092 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19079 eq64
    | (have r₁ := eq64
       have r₂ := eq19079
       grind)
    | exact resolve eq64 eq19079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq19099 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) (M.op X0 (M.op (σ y) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19079 eq1059
    | exact resolve eq1059 eq19079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19115 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19092
  have eq19445 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19115 eq115
    | exact resolve eq115 eq19115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq19465 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq19445
  have eq19973 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18145 eq57
    | exact resolve eq57 eq18145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq18145
  have eq20015 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq19973
    | exact resolve eq19973 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19973
  have eq20286 : (τ (σ y)) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20015 eq16627
    | exact resolve eq16627 eq20015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16627
  have eq20293 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20015 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20015
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20015
       grind)
    | exact resolve eq13 eq20015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20331 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq20293
  have eq20336 : (τ (σ y)) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq20286
  have eq20347 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq20331
    | exact resolve eq20331 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20331
  have eq20353 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq20336
       have r₂ := eq19090
       grind)
    | exact resolve eq20336 eq19090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20336
  have eq20354 : y = (k y x) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq29 eq20353
    | exact resolve eq20353 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20353
  have eq20398 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq19465 eq20015
    | exact resolve eq20015 eq19465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20440 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq20398
  have eq20454 : y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq20440
       have r₂ := eq75
       grind)
    | exact resolve eq20440 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20440
  have eq20465 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq20354
       grind)
    | exact superpose eq20354 eq72
    | exact resolve eq72 eq20354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20354
  have eq20500 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq20465
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20465
    | exact resolve eq20465 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20465
  have eq20595 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq20454
       grind)
    | exact superpose eq20454 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq20454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20454
  have eq20605 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20595
  have eq20613 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20605
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20605
    | exact resolve eq20605 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20605
  have eq20660 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20613
       grind)
    | exact superpose eq20613 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20613
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20613
       grind)
    | exact resolve eq13 eq20613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20613
  have eq20698 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20660
  have eq20710 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20698
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20698
    | exact resolve eq20698 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20698
  have eq20718 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20710
       grind)
    | exact superpose eq20710 eq44
    | exact resolve eq44 eq20710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20747 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq20718
    | exact resolve eq20718 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20718
  have eq20847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20747 eq20347
    | exact resolve eq20347 eq20747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20347 eq20747
  have eq20855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20847
  have eq20866 : y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq20855
       have r₂ := eq27
       grind)
    | exact resolve eq20855 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20855
  have eq21015 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20710
       have i₂ := eq20866
       grind)
    | exact superpose eq20866 eq20710
    | exact resolve eq20710 eq20866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20710 eq20866
  have eq21027 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq21015
  have eq21073 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21027 eq29
    | exact resolve eq29 eq21027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21027
  have eq21280 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq21073
    | exact resolve eq21073 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq21073
  have eq21281 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21280
  have eq21287 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21281 eq20
    | exact resolve eq20 eq21281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21289 : ∀ X0 : G, (M.op y (M.op X0 (M.op y X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21281 eq50
    | exact resolve eq50 eq21281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq21304 : (σ (k y x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21281 eq132
    | exact resolve eq132 eq21281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq21359 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq21396 : (k (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21304
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq21304
    | exact resolve eq21304 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21304
  have eq21412 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21287
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21287
    | exact resolve eq21287 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21287
  have eq21733 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21396 eq19115
    | exact resolve eq19115 eq21396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19115 eq21396
  have eq21743 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq21733
  have eq35731 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21412 eq20500
    | exact resolve eq20500 eq21412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20500 eq21412
  have eq35797 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq35731
  have eq41380 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3743 eq21289
    | exact resolve eq21289 eq3743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3743
  have eq41769 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq35797 eq21743
    | exact resolve eq21743 eq35797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21743 eq35797
  have eq41784 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq41769
  have eq91419 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20015 eq19099
    | exact resolve eq19099 eq20015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19099 eq20015
  have eq91565 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq91419
  have eq91660 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq91565
    | exact resolve eq91565 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91565
  have eq91685 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19079 eq91660
    | exact resolve eq91660 eq19079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19079 eq91660
  have eq91770 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq91685
  have eq91838 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq91770 eq19465
    | exact resolve eq19465 eq91770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19465
  have eq91847 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq91770 eq41784
    | exact resolve eq41784 eq91770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41784 eq91770
  have eq91912 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq91847
  have eq91921 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by grind
  clear eq91838
  have eq91967 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq91912
       have r₂ := eq19090
       grind)
    | exact resolve eq91912 eq19090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91912
  have eq91969 : x = (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | (have r₁ := eq91921
       have r₂ := eq19090
       grind)
    | exact resolve eq91921 eq19090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19090 eq91921
  have eq91983 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq91969
       have r₂ := eq75
       grind)
    | exact resolve eq91969 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq91969
  have eq92013 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq91967
       grind)
    | exact superpose eq91967 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq91967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91967
  have eq92023 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq92013
  have eq92046 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92023
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92023
    | exact resolve eq92023 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92023
  have eq92047 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq92046
  have eq92091 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21289 x
       have i₂ := eq92047
       grind)
    | exact superpose eq92047 eq21289
    | exact resolve eq21289 eq92047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21289 eq92047
  have eq92146 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq92091
  have eq92179 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92146
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92146
    | exact resolve eq92146 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92146
  have eq92508 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21281 eq92179
    | exact resolve eq92179 eq21281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21281
  have eq92529 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92179 eq41380
    | exact resolve eq41380 eq92179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41380 eq92179
  have eq92579 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq92529
  have eq92604 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92579
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92579
    | exact resolve eq92579 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92579
  have eq92612 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq92508
       have r₂ := eq21359
       grind)
    | exact resolve eq92508 eq21359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21359 eq92508
  have eq93283 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92604
       have i₂ := eq92612
       grind)
    | exact superpose eq92612 eq92604
    | exact resolve eq92604 eq92612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92604 eq92612
  have eq93344 : x = (M.op x y) := by grind
  clear eq93283
  have eq93373 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq93344 eq20
    | exact resolve eq20 eq93344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq93377 : x ≠ x ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq93344 eq63
    | (have r₁ := eq63
       have r₂ := eq93344
       grind)
    | exact resolve eq63 eq93344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq93519 : (k y x) = (M.op y x) := by grind
  clear eq93377
  have eq93630 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq93373
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq93373
    | exact resolve eq93373 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93373
  have eq93674 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq93630 eq26
    | exact resolve eq26 eq93630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94098 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq93519
       grind)
    | exact superpose eq93519 eq72
    | exact resolve eq72 eq93519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq93519
  have eq94146 : (k (σ y) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq93630 eq94098
    | exact resolve eq94098 eq93630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94098
  have eq96361 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq852 y x
       have i₂ := eq91983
       grind)
    | exact superpose eq91983 eq852
    | (have j0 := eq852 y x
       grind)
    | exact resolve eq852 eq91983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq96362 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq865 x y
       have i₂ := eq91983
       grind)
    | exact superpose eq91983 eq865
    | (have j0 := eq865 x y
       grind)
    | exact resolve eq865 eq91983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq91983
  have eq96365 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq96362
  have eq96366 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq96361
  have eq96370 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96365
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq96365
    | exact resolve eq96365 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96365
  have eq96371 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96366
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq96366
    | exact resolve eq96366 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96366
  have eq96390 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96370
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96370
    | exact resolve eq96370 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96370
  have eq96391 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96371
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96371
    | exact resolve eq96371 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96371
  have eq96407 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq96390
    | exact resolve eq96390 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96390
  have eq96408 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq96391
    | exact resolve eq96391 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96391
  have eq96417 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96407
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq96407
    | exact resolve eq96407 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96407
  have eq96418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq93630 eq96408
    | exact resolve eq96408 eq93630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96408
  have eq96423 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96417
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96417
    | exact resolve eq96417 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96417
  have eq96424 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq96418
       have r₂ := eq27
       grind)
    | exact resolve eq96418 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96418
  have eq96429 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq96423
    | exact resolve eq96423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq96423
  have eq96430 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96424
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96424
    | exact resolve eq96424 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96424
  have eq96435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq93630 eq96429
    | exact resolve eq96429 eq93630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96429
  have eq96436 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq93630 eq96430
    | exact resolve eq96430 eq93630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96430
  have eq96441 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq96435
       have r₂ := eq27
       grind)
    | exact resolve eq96435 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96435
  have eq96442 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96436
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq96436
    | exact resolve eq96436 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96436
  have eq96459 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq94146
       have i₂ := eq96441
       grind)
    | exact superpose eq96441 eq94146
    | exact resolve eq94146 eq96441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94146
  have eq96468 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq96441
       grind)
    | exact superpose eq96441 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq96441
       grind)
    | exact resolve eq13 eq96441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96441
  have eq96516 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq96468
  have eq96547 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq96516
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96516
    | exact resolve eq96516 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96516
  have eq96554 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq96459
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq96459
    | exact resolve eq96459 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96459
  have eq96581 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93344 eq96547
    | exact resolve eq96547 eq93344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96547
  have eq97197 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq96581
       grind)
    | exact superpose eq96581 eq44
    | exact resolve eq44 eq96581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq96581
  have eq97265 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93630 eq97197
    | exact resolve eq97197 eq93630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97197
  have eq97283 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97265
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq97265
    | exact resolve eq97265 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97265
  have eq97299 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93630 eq97283
    | exact resolve eq97283 eq93630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97283
  have eq97570 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96554 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq96554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96554
  have eq97582 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93674 eq97570
    | exact resolve eq97570 eq93674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97570
  have eq97583 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq97582
  have eq97596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq93674 eq97583
    | exact resolve eq97583 eq93674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97583
  have eq97607 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq97596
       have r₂ := eq27
       grind)
    | exact resolve eq97596 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97596
  have eq98292 : (σ y) ≠ (σ y) ∨ (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq97607 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ y)
       have r₂ := eq97607
       grind)
    | exact resolve eq13 eq97607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97607
  have eq98341 : (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq98292
  have eq98377 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93674 eq98341
    | exact resolve eq98341 eq93674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98341
  have eq98583 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98377 eq97299
    | exact resolve eq97299 eq98377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97299 eq98377
  have eq98597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq98583
  have eq98606 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq98597
       have r₂ := eq27
       grind)
    | exact resolve eq98597 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98597
  have eq98622 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq98606 eq27
    | exact resolve eq27 eq98606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98623 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq98606 eq51
    | exact resolve eq51 eq98606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq99310 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq3875 eq98623
    | exact resolve eq98623 eq3875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3875 eq98623
  have eq99423 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq98606 eq99310
    | exact resolve eq99310 eq98606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99310
  have eq99822 : (σ (M.op x y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq96442 eq1059
    | exact resolve eq1059 eq96442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059 eq96442
  have eq99913 : (σ (M.op x y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq93674 eq99822
    | exact resolve eq99822 eq93674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99822
  have eq99950 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq98606 eq99913
    | exact resolve eq99913 eq98606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98606 eq99913
  have eq99961 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq99423 eq99950
    | exact resolve eq99950 eq99423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99950
  have eq100106 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq99961 eq99423
    | exact resolve eq99423 eq99961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99423 eq99961
  have eq100182 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq93674 eq100106
    | exact resolve eq100106 eq93674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93674 eq100106
  have eq100212 : y = (M.op y x) := by
    first
    | (have r₁ := eq100182
       have r₂ := eq27
       grind)
    | exact resolve eq100182 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq100182
  have eq100245 : x = (M.op (M.op y (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq1048 x
       have i₂ := eq100212
       grind)
    | exact superpose eq100212 eq1048
    | exact resolve eq1048 eq100212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq100334 : x = (M.op (M.op y (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq100245
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100245
    | exact resolve eq100245 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq100245
  have eq100370 : x = (M.op (M.op y x) x) := by
    first
    | exact superpose eq93344 eq100334
    | exact resolve eq100334 eq93344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93344 eq100334
  have eq100381 : x = (M.op y x) := by
    first
    | (have i₁ := eq100370
       have i₂ := eq100212
       grind)
    | exact superpose eq100212 eq100370
    | exact resolve eq100370 eq100212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100370
  have eq100388 : x = y := by
    first
    | (have i₁ := eq100381
       have i₂ := eq100212
       grind)
    | exact superpose eq100212 eq100381
    | exact resolve eq100381 eq100212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100212 eq100381
  have eq100397 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq100388
       grind)
    | exact superpose eq100388 eq24
    | exact resolve eq24 eq100388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq100388
  have eq100766 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq100397
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq100397
    | exact resolve eq100397 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq100397
  have eq100880 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq93630 eq100766
    | exact resolve eq100766 eq93630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93630 eq100766
  have eq100957 : False := by grind
  exact eq100957

/-- `Equation72`: `x = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pyx_pxy_x_pyx_Equation72 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law72 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law72.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq36 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op x y)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq47 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq46 (M.op X0 X0)
       grind)
    | exact superpose eq46 eq9
    | exact resolve eq9 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq48
    | exact resolve eq48 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (τ (k (k (σ X0) (σ X1)) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 (k X0 X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq26 eq48
    | (have j0 := eq48 (M.op x y) X0
       grind)
    | exact resolve eq48 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq48
    | exact resolve eq48 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (k X2 (k X0 X1)) = (τ (k (σ X2) (k (σ X0) (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X2 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq26 eq48
    | (have j0 := eq48 X0 (M.op x y)
       grind)
    | exact resolve eq48 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq53
    | exact resolve eq53 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k (M.op x y) (k X0 X1)) = (τ (k (σ (M.op x y)) (k (σ X0) (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq53
    | exact resolve eq53 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq58 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq58
    | exact resolve eq58 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq46 X0
       grind)
    | exact resolve eq13 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq85 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq73 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq87
    | (have j0 := eq87 X0
       grind)
    | exact resolve eq87 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq89 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq88
    | (have j0 := eq88 X0
       grind)
    | exact resolve eq88 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq90 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq89
    | (have j0 := eq89 X0
       grind)
    | exact resolve eq89 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq108 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq14
    | (have j0 := eq14 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq73 sF5
       grind)
    | exact superpose eq73 eq110
    | exact resolve eq110 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq129 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq108
       have i₂ := eq73 (τ sF5)
       grind)
    | exact superpose eq73 eq108
    | exact resolve eq108 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq138 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq73 sF4
       grind)
    | exact superpose eq73 eq127
    | exact resolve eq127 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq140 : (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq129
       have i₂ := eq73 (τ sF4)
       grind)
    | exact superpose eq73 eq129
    | exact resolve eq129 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq149 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq138
       have i₂ := eq73 sF5
       grind)
    | exact superpose eq73 eq138
    | exact resolve eq138 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq151 : (k (τ (σ y)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq73 (τ sF5)
       grind)
    | exact superpose eq73 eq140
    | exact resolve eq140 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq178 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq49
    | exact resolve eq49 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X1) = (k X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq46
    | exact resolve eq46 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq73 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (M.op (k X0 X0) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq222 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq222
    | exact resolve eq222 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq224 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq219
    | (have j0 := eq219 X0 X1
       grind)
    | (have r₁ := eq219 X0 X0
       have r₂ := eq73 X0
       grind)
    | exact resolve eq219 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq226 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq217
    | (have j0 := eq217 X0 X1
       grind)
    | (have r₁ := eq217 X0 X0
       have r₂ := eq73 X0
       grind)
    | exact resolve eq217 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq285 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq149 eq178
    | exact resolve eq178 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : (k (σ (σ y)) (σ (σ y))) = (σ (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq149 eq15
    | exact resolve eq15 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : (k (σ (σ y)) (σ (σ y))) = (k (σ (σ x)) (σ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq286
       have i₂ := eq15 sF4 sF4
       grind)
    | exact superpose eq15 eq286
    | exact resolve eq286 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq288 : (k (τ (σ y)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq285
       have i₂ := eq178 sF4 sF4
       grind)
    | exact superpose eq178 eq285
    | exact resolve eq285 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq460 : (k (τ (τ (σ y))) (τ (τ (σ y)))) = (τ (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq151 eq178
    | exact resolve eq178 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq151 eq15
    | exact resolve eq15 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq461
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq461
    | exact resolve eq461 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq464 : (k (τ (τ (σ y))) (τ (τ (σ y)))) = (k (τ (τ (σ x))) (τ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq460
       have i₂ := eq178 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq178 eq460
    | exact resolve eq460 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq465 : (k (σ x) (σ x)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq463
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq463
    | exact resolve eq463 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq466 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq465
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq465
    | exact resolve eq465 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq487 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq466 eq15
    | exact resolve eq15 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq489 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq487
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq487
    | exact resolve eq487 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq490 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq489
    | exact resolve eq489 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq511 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq490 eq15
    | exact resolve eq15 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq512 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq511
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq511
    | exact resolve eq511 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq513 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq512
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq512
    | exact resolve eq512 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq514 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq513
    | exact resolve eq513 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq519 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq514 eq178
    | exact resolve eq178 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : (k (τ (σ y)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq519
       have i₂ := eq178 sF4 sF4
       grind)
    | exact superpose eq178 eq519
    | exact resolve eq519 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq602 : ∀ X0 : G, (M.op (k (M.op X0 X0) (M.op X0 X0)) (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (k (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq220 (M.op X0 X0)
       grind)
    | exact superpose eq220 eq9
    | exact resolve eq9 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 : G, (k (k (M.op X0 X0) (M.op X0 X0)) (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq602 X0
       have i₂ := eq73 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq73 eq602
    | exact resolve eq602 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq606 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq603 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq603
    | exact resolve eq603 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq627 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (M.op X0 (k (τ (σ x)) (τ (σ x))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq522 eq221
    | exact resolve eq221 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq630 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (M.op X0 (k (τ (σ x)) (τ (σ x))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq288 eq221
    | exact resolve eq221 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq631 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (k (σ x) (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq514 eq221
    | exact resolve eq221 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq632 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (k (σ x) (σ x)))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq149 eq221
    | exact resolve eq221 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq648 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq632 x
       have i₂ := eq221 sF4 x
       grind)
    | exact superpose eq221 eq632
    | exact resolve eq632 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq649 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq631 x
       have i₂ := eq221 sF4 x
       grind)
    | exact superpose eq221 eq631
    | exact resolve eq631 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq650 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq630 x
       have i₂ := eq221 (τ sF4) x
       grind)
    | exact superpose eq221 eq630
    | exact resolve eq630 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq652 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq627 x
       have i₂ := eq221 (τ sF4) x
       grind)
    | exact superpose eq221 eq627
    | exact resolve eq627 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq663 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq649 eq36
    | exact resolve eq36 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq679 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq663
       have i₂ := eq178 sF5 sF5
       grind)
    | exact superpose eq178 eq663
    | exact resolve eq663 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq716 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq652 eq36
    | exact resolve eq36 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq735 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq716
       have i₂ := eq178 sF5 sF5
       grind)
    | exact superpose eq178 eq716
    | exact resolve eq716 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq756 : ∀ X0 : G, (k X0 X0) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq151 eq224
    | (have j0 := eq224 X0 (τ (σ x))
       grind)
    | (have r₁ := eq224 (τ (σ y)) (τ (σ x))
       have r₂ := eq151
       grind)
    | (have r₁ := eq224 (τ (σ x)) (τ (σ y))
       have r₂ := eq151
       grind)
    | exact resolve eq224 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq224
  have eq794 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq9
    | exact resolve eq9 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq9
    | exact resolve eq9 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq46 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq46
    | exact resolve eq46 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq47
  have eq802 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq799 X0
       have i₂ := eq73 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq799
    | exact resolve eq799 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq806 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq73 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq795
    | exact resolve eq795 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq807 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq794 X0
       have i₂ := eq73 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq794
    | exact resolve eq794 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq812 : ∀ X0 : G, (M.op X0 (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq802 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq802
    | exact resolve eq802 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq816 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq806
    | exact resolve eq806 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq817 : ∀ X0 : G, (k X0 X0) = (M.op (k (k X0 X0) (k X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq807 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq807
    | exact resolve eq807 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq837 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (M.op X0 (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq679 eq221
    | exact resolve eq221 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq846 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq837 x
       have i₂ := eq816 sF2 x
       grind)
    | exact superpose eq816 eq837
    | exact resolve eq837 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq865 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq223 X0
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq223
    | (have j1 := eq90 X0
       grind)
    | exact resolve eq223 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k (k X0 X0) (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq223 (k X0 X0)
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq223
    | (have j1 := eq90 X0
       grind)
    | exact resolve eq223 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq882 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq874 X0
       have i₂ := eq223 X0
       grind)
    | exact superpose eq223 eq874
    | (have j0 := eq874 X0
       grind)
    | exact resolve eq874 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq887 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq865 X0
       have i₂ := eq73 (k X0 X0)
       grind)
    | exact superpose eq73 eq865
    | (have j0 := eq865 X0
       grind)
    | exact resolve eq865 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq909 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq226
    | (have j0 := eq226 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq226 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq226
    | (have j0 := eq226 (σ y) (σ x)
       grind)
    | exact resolve eq226 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq963 : (k (σ (σ (σ y))) (σ (σ (σ y)))) = (σ (k (σ (σ x)) (σ (σ x)))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq287 eq15
    | exact resolve eq15 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq964 : (k (σ (σ (σ y))) (σ (σ (σ y)))) = (k (σ (σ (σ x))) (σ (σ (σ x)))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq963
       have i₂ := eq15 (σ sF4) (σ sF4)
       grind)
    | exact superpose eq15 eq963
    | exact resolve eq963 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq992 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (M.op X0 (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq735 eq221
    | exact resolve eq221 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq1001 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq992 x
       have i₂ := eq816 sF2 x
       grind)
    | exact superpose eq816 eq992
    | exact resolve eq992 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1277 : (σ y) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq846 eq35
    | exact resolve eq35 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq1287 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1277
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq1277
    | exact resolve eq1277 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq1290 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1287
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1287
    | exact resolve eq1287 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1293 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq1290
    | exact resolve eq1290 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq3611 : (σ y) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1001 eq35
    | exact resolve eq35 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3612 : (τ (σ x)) ≠ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1001
  have eq3627 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq3611
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq3611
    | exact resolve eq3611 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3611
  have eq3633 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq3627
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq3627
    | exact resolve eq3627 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3627
  have eq3639 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq26 eq3633
    | exact resolve eq3633 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3633
  have eq5713 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq3639 eq812
    | exact resolve eq812 eq3639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3639
  have eq5714 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1293 eq812
    | exact resolve eq812 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq1293
  have eq5876 : ∀ X0 : G, (τ (σ X0)) = (k X0 (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 X0 X0
       have i₂ := eq882 (σ X0)
       grind)
    | exact superpose eq882 eq55
    | (have j1 := eq882 (σ X0)
       grind)
    | exact resolve eq55 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5895 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5876 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq5876
    | (have j0 := eq5876 X0
       grind)
    | exact resolve eq5876 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq5876
  have eq5924 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k (k X0 X0) X1) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X0 X1
       have i₂ := eq5895 X0
       grind)
    | exact superpose eq5895 eq50
    | (have j1 := eq5895 X0
       grind)
    | exact resolve eq50 eq5895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5926 : ∀ X0 : G, (τ (k (σ (M.op x y)) (σ X0))) = (k (M.op x y) (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 X0 X0
       have i₂ := eq5895 X0
       grind)
    | exact superpose eq5895 eq65
    | (have j1 := eq5895 X0
       grind)
    | exact resolve eq65 eq5895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq5895
  have eq5977 : ∀ X0 : G, (k (M.op x y) X0) = (k (M.op x y) (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq53 eq5926
    | (have j0 := eq5926 X0
       grind)
    | exact resolve eq5926 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5926
  have eq5979 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X0) X1) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5924 X0 X1
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq5924
    | (have j0 := eq5924 X0 X1
       grind)
    | exact resolve eq5924 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5924
  have eq5987 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq648
  have eq6007 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq816 X0 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq816
    | exact resolve eq816 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6012 : ∀ X0 X1 : G, (M.op X1 (k (k X0 X0) (k X0 X0))) = (k (k (M.op X1 X0) (M.op X1 X0)) (k (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq816 (M.op X1 X0) X1
       have i₂ := eq816 X0 X1
       grind)
    | exact superpose eq816 eq816
    | exact resolve eq816 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6043 : (k (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32 eq816
    | (have j0 := eq816 (σ y) (σ x)
       grind)
    | exact resolve eq816 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6120 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq5713 eq36
    | exact resolve eq36 eq5713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6121 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (k (σ y) (σ x)) (σ X0))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq5713 eq53
    | exact resolve eq53 eq5713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5713
  have eq6138 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (k (σ y) (σ x))) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6121 x
       have i₂ := eq49 (k sF5 sF4) x
       grind)
    | exact superpose eq49 eq6121
    | exact resolve eq6121 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6121
  have eq6139 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq6120
       have i₂ := eq178 sF4 sF5
       grind)
    | exact superpose eq178 eq6120
    | exact resolve eq6120 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6120
  have eq6146 : ∀ X0 : G, (k (M.op x y) X0) = (k (k (τ (σ y)) (τ (σ x))) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6138 X0
       have i₂ := eq178 sF4 sF5
       grind)
    | exact superpose eq178 eq6138
    | exact resolve eq6138 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6138
  have eq6840 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have j0 := eq5977 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5977
  have eq6842 : (M.op x y) = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have j1 := eq882 (M.op x y)
       grind)
    | (have r₁ := eq6840
       have r₂ := eq882 (M.op x y)
       grind)
    | exact resolve eq6840 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq6840
  have eq6853 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq6842 eq15
    | exact resolve eq15 eq6842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6842
  have eq6854 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq6853
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq6853
    | exact resolve eq6853 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6853
  have eq6856 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq26 eq6854
    | exact resolve eq6854 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6854
  have eq6858 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq650 eq916
    | (have r₁ := eq916
       have r₂ := eq650
       grind)
    | exact resolve eq916 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq916
  have eq6865 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq6858
  have eq7337 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq887 X0
       have i₂ := eq5979 X0 (k X0 X0)
       grind)
    | exact superpose eq5979 eq887
    | (have j0 := eq887 X0
       have j1 := eq5979 X0 x
       grind)
    | exact resolve eq887 eq5979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq5979
  have eq7416 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq7337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7337
  have eq7466 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (k (k (k X0 X0) (k X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq7416 (k (k X0 X0) (k X0 X0))
       have i₂ := eq606 X0
       grind)
    | exact superpose eq606 eq7416
    | exact resolve eq7416 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8715 : (σ (σ (σ y))) = (k (k (k (σ (σ (σ x))) (σ (σ (σ x)))) (k (σ (σ (σ x))) (σ (σ (σ x))))) (k (k (σ (σ (σ x))) (σ (σ (σ x)))) (k (σ (σ (σ x))) (σ (σ (σ x)))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq964 eq606
    | exact resolve eq606 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq8748 : (σ (σ (σ y))) = (σ (σ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8715
       have i₂ := eq606 (σ (σ sF4))
       grind)
    | exact superpose eq606 eq8715
    | exact resolve eq8715 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8715
  have eq109446 : (σ y) = (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq6865 eq606
    | exact resolve eq606 eq6865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865
  have eq109598 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109446
       have i₂ := eq606 sF4
       grind)
    | exact superpose eq606 eq109446
    | exact resolve eq109446 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109446
  have eq109611 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq109598 eq33
    | exact resolve eq33 eq109598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109598
  have eq110103 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5714 eq109611
    | (have r₁ := eq109611
       have r₂ := eq5714
       grind)
    | exact resolve eq109611 eq5714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5714
  have eq110113 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq110103
  have eq110114 : (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq110113
  have eq110153 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq110114 eq178
    | exact resolve eq178 eq110114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110114
  have eq118351 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq110153 eq6146
    | exact resolve eq6146 eq110153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6146
  have eq118399 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq118351 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118351
  have eq119819 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq118399 eq6139
    | exact resolve eq6139 eq118399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6139
  have eq119845 : (τ (σ y)) = (k (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq118399 eq110153
    | exact resolve eq110153 eq118399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110153 eq118399
  have eq120065 : (τ (σ y)) = (k (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq119845
  have eq120090 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq119819
  have eq120191 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq120090 eq15
    | exact resolve eq15 eq120090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120090
  have eq120192 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120191
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq120191
    | exact resolve eq120191 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120191
  have eq120195 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq120192
    | exact resolve eq120192 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120192
  have eq120736 : (σ y) = (σ (k (M.op x y) (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq120065 eq35
    | exact resolve eq35 eq120065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120065
  have eq120842 : (σ y) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq120736
       have i₂ := eq15 sF2 (τ sF4)
       grind)
    | exact superpose eq15 eq120736
    | exact resolve eq120736 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120736
  have eq120867 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq120842
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq120842
    | exact resolve eq120842 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120842
  have eq120875 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq120867
    | exact resolve eq120867 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120867
  have eq121047 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq120875 eq120195
    | exact resolve eq120195 eq120875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120195 eq120875
  have eq121066 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq121047
  have eq121104 : (k (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq121066 eq816
    | exact resolve eq816 eq121066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121066
  have eq121117 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq121104
       have i₂ := eq73 sF3
       grind)
    | exact superpose eq73 eq121104
    | exact resolve eq121104 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121104
  have eq238884 : (τ (τ (σ y))) = (k (k (k (τ (τ (σ x))) (τ (τ (σ x)))) (k (τ (τ (σ x))) (τ (τ (σ x))))) (k (k (τ (τ (σ x))) (τ (τ (σ x)))) (k (τ (τ (σ x))) (τ (τ (σ x)))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq464 eq606
    | exact resolve eq606 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq238912 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (τ (σ y))) = (τ (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq238884
       have i₂ := eq606 (τ (τ sF4))
       grind)
    | exact superpose eq606 eq238884
    | exact resolve eq238884 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238884
  have eq239048 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (τ (τ (σ y))) = (τ (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq238912 eq15
    | exact resolve eq15 eq238912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238912
  have eq239053 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (τ (σ y))) = (τ (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq239048
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq239048
    | exact resolve eq239048 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239048
  have eq239065 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (τ (σ y))) = (τ (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq239053
    | exact resolve eq239053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239053
  have eq239101 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (τ (σ y))) = (τ (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq239065 eq15
    | exact resolve eq15 eq239065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239065
  have eq239102 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (τ (σ y))) = (τ (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq239101
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq239101
    | exact resolve eq239101 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239101
  have eq239103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (τ (σ y))) = (τ (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq239102
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq239102
    | exact resolve eq239102 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239102
  have eq239104 : (τ (τ (σ y))) = (τ (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq239103
    | exact resolve eq239103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239103
  have eq245960 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have j0 := eq756 (τ (σ x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq245966 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq245960
    | exact resolve eq245960 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245960
  have eq246088 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq245966 eq15
    | exact resolve eq15 eq245966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245966
  have eq246095 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq246088
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq246088
    | exact resolve eq246088 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246088
  have eq246104 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq246095
    | exact resolve eq246095 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246095
  have eq246137 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq246104 eq15
    | exact resolve eq15 eq246104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246104
  have eq246140 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq246137
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq246137
    | exact resolve eq246137 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246137
  have eq246141 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq246140
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq246140
    | exact resolve eq246140 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246140
  have eq246142 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq246141
    | exact resolve eq246141 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246141
  have eq246290 : (τ (M.op x y)) = (k (τ (τ (σ x))) (τ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq246142 eq178
    | exact resolve eq178 eq246142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246142
  have eq249243 : (k (τ (τ (σ x))) (τ (τ (σ x)))) = (τ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq239104 eq246290
    | exact resolve eq246290 eq239104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239104 eq246290
  have eq249248 : (k (τ (τ (σ x))) (τ (τ (σ x)))) = (τ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq249243
  have eq249394 : (σ (τ (M.op x y))) = (k (σ (τ (τ (σ x)))) (σ (τ (τ (σ x))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq249248 eq15
    | exact resolve eq15 eq249248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249248
  have eq249399 : (k (τ (σ x)) (τ (σ x))) = (σ (τ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq249394
       have i₂ := eq35 (τ sF4)
       grind)
    | exact superpose eq35 eq249394
    | exact resolve eq249394 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249394
  have eq249407 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq249399
       have i₂ := eq35 sF2
       grind)
    | exact superpose eq35 eq249399
    | exact resolve eq249399 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249399
  have eq249476 : (τ (σ x)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq249407 eq606
    | exact resolve eq606 eq249407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249407
  have eq258145 : (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ≠ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq249476 eq3612
    | (have r₁ := eq3612
       have r₂ := eq249476
       grind)
    | exact resolve eq3612 eq249476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3612 eq249476
  have eq258266 : (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ≠ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq258145
  have eq258267 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq258266
  have eq261521 : (σ y) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq258267 eq35
    | exact resolve eq35 eq258267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258267
  have eq261643 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq261521
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq261521
    | exact resolve eq261521 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261521
  have eq261652 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq261643
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq261643
    | exact resolve eq261643 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261643
  have eq261659 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq261652
    | exact resolve eq261652 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261652
  have eq261741 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq261659 eq606
    | exact resolve eq606 eq261659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261659
  have eq261864 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq261741
  have eq261924 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq261864 eq36
    | exact resolve eq36 eq261864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261925 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (k (σ y) (σ y)) (σ X0))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq261864 eq53
    | exact resolve eq53 eq261864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq261926 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq261864 eq58
    | exact resolve eq58 eq261864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq262398 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  have eq262522 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq261926 x
       have i₂ := eq54 (k sF5 sF5) x
       grind)
    | exact superpose eq54 eq261926
    | exact resolve eq261926 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261926
  have eq262523 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (k (σ y) (σ y))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq261925 x
       have i₂ := eq49 (k sF5 sF5) x
       grind)
    | exact superpose eq49 eq261925
    | exact resolve eq261925 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261925
  have eq262524 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq261924
       have i₂ := eq178 sF5 sF5
       grind)
    | exact superpose eq178 eq261924
    | exact resolve eq261924 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261924
  have eq262594 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (k (τ (σ y)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq262522 X0
       have i₂ := eq178 sF5 sF5
       grind)
    | exact superpose eq178 eq262522
    | exact resolve eq262522 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262522
  have eq262595 : ∀ X0 : G, (k (M.op x y) X0) = (k (k (τ (σ y)) (τ (σ y))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq262523 X0
       have i₂ := eq178 sF5 sF5
       grind)
    | exact superpose eq178 eq262523
    | exact resolve eq262523 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262523
  have eq262652 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq262524 eq909
    | (have r₁ := eq909
       have r₂ := eq262524
       grind)
    | exact resolve eq909 eq262524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq262718 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq262524 eq606
    | exact resolve eq606 eq262524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262795 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq262524 eq7416
    | exact resolve eq7416 eq262524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262837 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq262652
  have eq262934 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq262795 eq15
    | exact resolve eq15 eq262795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262795
  have eq262949 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq262934
    | exact resolve eq262934 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262934
  have eq262950 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq262949
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq262949
    | exact resolve eq262949 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262949
  have eq263034 : (σ (σ y)) = (k (σ (σ y)) (σ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq262950 eq15
    | exact resolve eq15 eq262950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262950
  have eq263139 : ∀ X0 : G, (k X0 (k (σ y) (σ (M.op x y)))) = (τ (k (σ X0) (σ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq263034 eq55
    | exact resolve eq55 eq263034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263140 : ∀ X0 : G, (k (k (σ y) (σ (M.op x y))) X0) = (τ (k (σ (σ y)) (σ X0))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq263034 eq50
    | exact resolve eq50 eq263034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263034
  have eq263172 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ y) (σ (M.op x y))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq263140 x
       have i₂ := eq48 sF5 x
       grind)
    | exact superpose eq48 eq263140
    | exact resolve eq263140 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263140
  have eq263173 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (k (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq263139 X0
       have i₂ := eq48 X0 sF5
       grind)
    | exact superpose eq48 eq263139
    | exact resolve eq263139 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263139
  have eq263647 : (k (σ y) (σ (M.op x y))) = (k (k (σ y) (σ (M.op x y))) (k (σ y) (k (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq263172 eq7416
    | exact resolve eq7416 eq263172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265117 : (σ y) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq262718 eq35
    | exact resolve eq35 eq262718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265264 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq265117
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq265117
    | exact resolve eq265117 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265117
  have eq265330 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq265264
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq265264
    | exact resolve eq265264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265264
  have eq265367 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq265330
    | exact resolve eq265330 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265330
  have eq265472 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq265367 eq817
    | exact resolve eq817 eq265367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq265520 : (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq265367 eq220
    | exact resolve eq220 eq265367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265522 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq265367 eq223
    | exact resolve eq223 eq265367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq265614 : (σ (σ y)) = (k (σ (k (σ (M.op x y)) (σ (M.op x y)))) (σ (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq265367 eq15
    | exact resolve eq15 eq265367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265657 : (σ (σ y)) = (k (k (σ (σ (M.op x y))) (σ (σ (M.op x y)))) (k (σ (σ (M.op x y))) (σ (σ (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq265614
       have i₂ := eq15 sF3 sF3
       grind)
    | exact superpose eq15 eq265614
    | exact resolve eq265614 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265614
  have eq265675 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq265522
       have i₂ := eq6007 sF5
       grind)
    | exact superpose eq6007 eq265522
    | exact resolve eq265522 eq6007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6007 eq265522
  have eq266008 : (k (σ (M.op x y)) (σ (M.op x y))) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq265472 eq226
    | (have j0 := eq226 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq226 (σ (M.op x y)) (σ y)
       have r₂ := eq265472
       grind)
    | exact resolve eq226 eq265472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq266010 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq266008
  have eq267039 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (k (τ (σ y)) (τ (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq262594 eq15
    | exact resolve eq15 eq262594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267245 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (σ (τ (σ y))) (σ (τ (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq267039 X0
       have i₂ := eq15 (τ sF5) (τ sF5)
       grind)
    | exact superpose eq15 eq267039
    | exact resolve eq267039 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267039
  have eq267260 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq267245 X0
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq267245
    | exact resolve eq267245 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267245
  have eq267262 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (k (σ X0) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq267260 X0
       have i₂ := eq15 X0 sF2
       grind)
    | exact superpose eq15 eq267260
    | exact resolve eq267260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267260
  have eq267263 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (k (σ X0) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq267262
    | (have j0 := eq267262 X0
       grind)
    | exact resolve eq267262 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267262
  have eq267455 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (k (τ (σ y)) (τ (σ y)))) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq262595 eq15
    | exact resolve eq15 eq262595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267620 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (k (σ (τ (σ y))) (σ (τ (σ y)))) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq267455 X0
       have i₂ := eq15 (τ sF5) (τ sF5)
       grind)
    | exact superpose eq15 eq267455
    | exact resolve eq267455 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267455
  have eq267634 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (k (σ y) (σ y)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq267620 X0
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq267620
    | exact resolve eq267620 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267620
  have eq267636 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (k (k (σ y) (σ y)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq267634 x
       have i₂ := eq15 sF2 x
       grind)
    | exact superpose eq15 eq267634
    | exact resolve eq267634 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267634
  have eq267637 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (k (k (σ y) (σ y)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq267636
    | (have j0 := eq267636 X0
       grind)
    | exact resolve eq267636 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267636
  have eq267638 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq267263 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq267263
    | exact resolve eq267263 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267263
  have eq268075 : (k (σ y) (σ (M.op x y))) = (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq267638 eq263172
    | exact resolve eq263172 eq267638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268128 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq267638 eq6856
    | exact resolve eq6856 eq267638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6856
  have eq268209 : (σ y) = (M.op (σ y) (k (σ (M.op x y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq267638 eq265520
    | exact resolve eq265520 eq267638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265520 eq267638
  have eq268408 : (σ y) = (M.op (σ y) (k (σ (M.op x y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq268209
  have eq268488 : (k (σ y) (σ (M.op x y))) = (k (k (σ y) (σ (M.op x y))) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq268075
  have eq269437 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (σ y) (σ y)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq267637 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq267637
    | exact resolve eq267637 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267637
  have eq269760 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (k (σ (M.op x y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq269437 eq268128
    | exact resolve eq268128 eq269437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268128
  have eq270303 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (k (σ (M.op x y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq269760
  have eq274816 : (τ (k (σ y) (σ (M.op x y)))) = (k (τ (k (σ y) (σ (M.op x y)))) (τ (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq268488 eq178
    | exact resolve eq178 eq268488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268488
  have eq274869 : (τ (k (σ y) (σ (M.op x y)))) = (k (τ (k (σ y) (σ (M.op x y)))) (k (τ (σ y)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq274816
       have i₂ := eq178 sF5 sF5
       grind)
    | exact superpose eq178 eq274816
    | exact resolve eq274816 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274816
  have eq274885 : (k (τ (σ y)) (M.op x y)) = (k (k (τ (σ y)) (M.op x y)) (k (τ (σ y)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq76 eq274869
    | exact resolve eq274869 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274869
  have eq279287 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq266010 eq7416
    | exact resolve eq7416 eq266010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266010
  have eq280873 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq279287 eq268408
    | exact resolve eq268408 eq279287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268408 eq279287
  have eq280923 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by grind
  clear eq280873
  have eq281009 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq280923 eq265472
    | exact resolve eq265472 eq280923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265472 eq280923
  have eq281016 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by grind
  clear eq281009
  have eq281509 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq281016 eq7416
    | exact resolve eq7416 eq281016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281016
  have eq281526 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by grind
  clear eq281509
  have eq281718 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq261864 eq281526
    | exact resolve eq281526 eq261864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281526
  have eq281869 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq281718
       have r₂ := eq262398
       grind)
    | exact resolve eq281718 eq262398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281718
  have eq281960 : (τ (k (σ y) (σ y))) = (k (τ (k (σ y) (σ y))) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq281869 eq178
    | exact resolve eq178 eq281869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281969 : (k (τ (σ y)) (τ (σ y))) = (k (k (τ (σ y)) (τ (σ y))) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq281960
       have i₂ := eq178 sF5 sF5
       grind)
    | exact superpose eq178 eq281960
    | exact resolve eq281960 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281960
  have eq288192 : (k (σ y) (σ (M.op x y))) = (k (σ y) (k (σ y) (k (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq263647 eq263172
    | exact resolve eq263172 eq263647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263172 eq263647
  have eq288199 : (k (σ y) (σ (M.op x y))) = (k (σ y) (k (σ y) (k (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq288192
  have eq292715 : (k (σ (σ y)) (σ (σ y))) = (σ (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq265657 eq606
    | exact resolve eq606 eq265657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265657
  have eq292931 : ∀ X0 X1 : G, (k (k (σ (M.op x y)) X0) X1) = (τ (k (k (k (σ (σ y)) (σ (σ y))) (σ X0)) (σ X1))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq292715 eq50
    | exact resolve eq50 eq292715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292936 : ∀ X0 X1 : G, (k X0 (k (σ (M.op x y)) X1)) = (τ (k (σ X0) (k (k (σ (σ y)) (σ (σ y))) (σ X1)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq292715 eq55
    | exact resolve eq55 eq292715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292715
  have eq293065 : ∀ X0 X1 : G, (k X0 (k (σ (M.op x y)) X1)) = (k X0 (τ (k (k (σ (σ y)) (σ (σ y))) (σ X1)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq292936 X1 X1
       have i₂ := eq54 (k (k (σ sF5) (σ sF5)) (σ X1)) X1
       grind)
    | exact superpose eq54 eq292936
    | exact resolve eq292936 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292936
  have eq293070 : ∀ X0 X1 : G, (k (k (σ (M.op x y)) X0) X1) = (k (τ (k (k (σ (σ y)) (σ (σ y))) (σ X0))) X1) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq292931 X0 X1
       have i₂ := eq49 (k (k (σ sF5) (σ sF5)) (σ X0)) X1
       grind)
    | exact superpose eq49 eq292931
    | exact resolve eq292931 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq292931
  have eq293098 : ∀ X0 X1 : G, (k X0 (k (σ (M.op x y)) X1)) = (k X0 (k (k (σ y) (σ y)) X1)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq293065 X0 x
       have i₂ := eq50 sF5 sF5 x
       grind)
    | exact superpose eq50 eq293065
    | exact resolve eq293065 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293065
  have eq293102 : ∀ X0 X1 : G, (k (k (k (σ y) (σ y)) X0) X1) = (k (k (σ (M.op x y)) X0) X1) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq293070 x X1
       have i₂ := eq50 sF5 sF5 x
       grind)
    | exact superpose eq50 eq293070
    | exact resolve eq293070 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293070
  have eq319761 : (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq262524 eq281969
    | exact resolve eq281969 eq262524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262524
  have eq319778 : (k (M.op x y) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq281969 eq262595
    | exact resolve eq262595 eq281969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281969
  have eq319791 : (k (M.op x y) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq319778
  have eq319801 : (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq319761
  have eq319823 : (M.op x y) = (k (M.op x y) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq262718 eq319801
    | exact resolve eq319801 eq262718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262718 eq319801
  have eq319834 : (M.op x y) = (k (M.op x y) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq319823
  have eq319960 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (k (M.op x y) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq319791 eq262594
    | exact resolve eq262594 eq319791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262594
  have eq319961 : ∀ X0 : G, (k (M.op x y) X0) = (k (k (M.op x y) (τ (σ y))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq319791 eq262595
    | exact resolve eq262595 eq319791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262595
  have eq320053 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (M.op x y) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq319791 eq15
    | exact resolve eq15 eq319791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320079 : ∀ X0 : G, (k (M.op x y) X0) = (k (k (M.op x y) (τ (σ y))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq319961 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319961
  have eq320080 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (k (M.op x y) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq319960 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319960
  have eq320136 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (M.op x y)) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq320053
       have i₂ := eq15 sF2 (τ sF5)
       grind)
    | exact superpose eq15 eq320053
    | exact resolve eq320053 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320053
  have eq320153 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq320136
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq320136
    | exact resolve eq320136 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320136
  have eq320158 : (k (σ (M.op x y)) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq320153
    | exact resolve eq320153 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320153
  have eq320267 : (σ (k (σ y) (σ y))) = (k (σ (σ (M.op x y))) (σ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq320158 eq15
    | exact resolve eq15 eq320158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320158
  have eq320303 : (k (σ (σ y)) (σ (σ y))) = (k (σ (σ (M.op x y))) (σ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq320267
       have i₂ := eq15 sF5 sF5
       grind)
    | exact superpose eq15 eq320267
    | exact resolve eq320267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320267
  have eq321245 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (k (M.op x y) (τ (σ y)))) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq320079 eq15
    | exact resolve eq15 eq320079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320079
  have eq321449 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (k (σ (M.op x y)) (σ (τ (σ y)))) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq321245 X0
       have i₂ := eq15 sF2 (τ sF5)
       grind)
    | exact superpose eq15 eq321245
    | exact resolve eq321245 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321245
  have eq321457 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (k (σ (M.op x y)) (σ y)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq321449 X0
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq321449
    | exact resolve eq321449 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321449
  have eq321458 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (k (σ (M.op x y)) (σ y)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq321457
    | (have j0 := eq321457 X0
       grind)
    | exact resolve eq321457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321457
  have eq321459 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (k (k (σ (M.op x y)) (σ y)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq321458 x
       have i₂ := eq15 sF2 x
       grind)
    | exact superpose eq15 eq321458
    | exact resolve eq321458 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321458
  have eq321460 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (k (k (σ (M.op x y)) (σ y)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq321459
    | (have j0 := eq321459 X0
       grind)
    | exact resolve eq321459 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321459
  have eq321581 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (k (M.op x y) (τ (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq320080 eq15
    | exact resolve eq15 eq320080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320080
  have eq321792 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (σ (M.op x y)) (σ (τ (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq321581 X0
       have i₂ := eq15 sF2 (τ sF5)
       grind)
    | exact superpose eq15 eq321581
    | exact resolve eq321581 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321581
  have eq321799 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq321792 X0
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq321792
    | exact resolve eq321792 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321792
  have eq321800 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq321799
    | (have j0 := eq321799 X0
       grind)
    | exact resolve eq321799 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321799
  have eq321801 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (k (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq321800 X0
       have i₂ := eq15 X0 sF2
       grind)
    | exact superpose eq15 eq321800
    | exact resolve eq321800 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321800
  have eq321802 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (k (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq321801
    | (have j0 := eq321801 X0
       grind)
    | exact resolve eq321801 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321801
  have eq321829 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq319834 eq15
    | exact resolve eq15 eq319834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319834
  have eq321835 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq321829
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq321829
    | exact resolve eq321829 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321829
  have eq321840 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq321835
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq321835
    | exact resolve eq321835 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321835
  have eq321843 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq321840
    | exact resolve eq321840 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321840
  have eq322030 : ∀ X0 : G, (τ (k (σ X0) (k (σ (σ y)) (σ (σ y))))) = (k X0 (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq320303 eq55
    | exact resolve eq55 eq320303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320303
  have eq322056 : ∀ X0 : G, (k X0 (k (σ y) (σ y))) = (k X0 (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq322030 x
       have i₂ := eq55 sF5 sF5 x
       grind)
    | exact superpose eq55 eq322030
    | exact resolve eq322030 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322030
  have eq322116 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (σ (M.op x y)) (σ y)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq321460 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq321460
    | exact resolve eq321460 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321460
  have eq322312 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (k (σ y) (σ y)) (σ y)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq322116 eq293102
    | exact resolve eq293102 eq322116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293102
  have eq322506 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (k (σ y) (σ y)) (σ y)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq322312 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322312
  have eq322865 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq321802 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq321802
    | exact resolve eq321802 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321802
  have eq323099 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (k (k (σ y) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq322865 eq293098
    | exact resolve eq293098 eq322865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293098 eq322865
  have eq323310 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (k (k (σ y) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq323099 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323099
  have eq323825 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq321843 eq269437
    | exact resolve eq269437 eq321843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321843
  have eq323847 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq323825
  have eq325815 : ∀ X0 : G, (τ (k (σ X0) (k (σ y) (σ y)))) = (k X0 (τ (k (σ (M.op x y)) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq322056 eq54
    | exact resolve eq54 eq322056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322056
  have eq326061 : ∀ X0 : G, (τ (k (σ X0) (k (σ y) (σ y)))) = (k X0 (k (M.op x y) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq64 eq325815
    | exact resolve eq325815 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq325815
  have eq326068 : ∀ X0 : G, (k X0 (τ (k (σ y) (σ y)))) = (k X0 (k (M.op x y) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq326061 x
       have i₂ := eq54 (k sF5 sF5) x
       grind)
    | exact superpose eq54 eq326061
    | exact resolve eq326061 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq326061
  have eq326072 : ∀ X0 : G, (k X0 (k (τ (σ y)) (τ (σ y)))) = (k X0 (k (M.op x y) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq326068 X0
       have i₂ := eq178 sF5 sF5
       grind)
    | exact superpose eq178 eq326068
    | exact resolve eq326068 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326068
  have eq327201 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (k (k (k (σ y) (σ y)) (σ y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq322506 eq270303
    | exact resolve eq270303 eq322506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270303 eq322506
  have eq327855 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (k (k (k (σ y) (σ y)) (σ y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq327201
  have eq338027 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq265367 eq323847
    | exact resolve eq323847 eq265367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265367 eq323847
  have eq338079 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq338027
  have eq338147 : (M.op x y) = (τ (k (k (σ y) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq338079 eq36
    | exact resolve eq36 eq338079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338079
  have eq338979 : (M.op x y) = (k (τ (k (σ y) (σ y))) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq338147
       have i₂ := eq178 sF5 (k sF5 sF5)
       grind)
    | exact superpose eq178 eq338147
    | exact resolve eq338147 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338147
  have eq339082 : (M.op x y) = (k (k (τ (σ y)) (τ (σ y))) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq338979
       have i₂ := eq178 sF5 sF5
       grind)
    | exact superpose eq178 eq338979
    | exact resolve eq338979 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338979
  have eq339242 : (M.op x y) = (k (k (M.op x y) (τ (σ y))) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq319791 eq339082
    | exact resolve eq339082 eq319791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319791 eq339082
  have eq339306 : (M.op x y) = (k (k (M.op x y) (τ (σ y))) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq339242
  have eq339351 : (σ (M.op x y)) = (k (σ (k (M.op x y) (τ (σ y)))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq339306 eq15
    | exact resolve eq15 eq339306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339306
  have eq339366 : (σ (M.op x y)) = (k (σ (k (M.op x y) (τ (σ y)))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq339351
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq339351
    | exact resolve eq339351 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339351
  have eq339367 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (τ (σ y)))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq339366
       have i₂ := eq15 sF2 (τ sF5)
       grind)
    | exact superpose eq15 eq339366
    | exact resolve eq339366 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339366
  have eq339368 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq339367
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq339367
    | exact resolve eq339367 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339367
  have eq339369 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq339368
    | exact resolve eq339368 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339368
  have eq428504 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq262837 eq15
    | exact resolve eq15 eq262837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262837
  have eq428508 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq428504
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq428504
    | exact resolve eq428504 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428504
  have eq428509 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq428508
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq428508
    | exact resolve eq428508 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428508
  have eq428531 : (τ (σ x)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq428509 eq606
    | exact resolve eq606 eq428509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428549 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq428509 eq15
    | exact resolve eq15 eq428509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428509
  have eq428560 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq428549
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq428549
    | exact resolve eq428549 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428549
  have eq428565 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq428560
    | exact resolve eq428560 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428560
  have eq431720 : (σ x) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq428531 eq35
    | exact resolve eq35 eq428531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428531
  have eq431721 : (σ x) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq431720
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq431720
    | exact resolve eq431720 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431720
  have eq431723 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq431721
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq431721
    | exact resolve eq431721 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431721
  have eq431724 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq431723
    | exact resolve eq431723 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431723
  have eq431816 : (σ x) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq431724 eq220
    | exact resolve eq220 eq431724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq431724
  have eq432548 : (σ x) = (M.op (σ x) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq265675 eq431816
    | exact resolve eq431816 eq265675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265675 eq431816
  have eq432619 : (σ x) = (M.op (σ x) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq432548
  have eq432633 : (σ x) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq432619
       have i₂ := eq6012 sF5 sF4
       grind)
    | exact superpose eq6012 eq432619
    | exact resolve eq432619 eq6012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6012 eq432619
  have eq432636 : (σ x) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq432633
    | exact resolve eq432633 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432633
  have eq434153 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq432636 eq606
    | exact resolve eq606 eq432636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq432636
  have eq434200 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq434153 eq33
    | exact resolve eq33 eq434153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434153
  have eq434224 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq434200
       have r₂ := eq428565
       grind)
    | exact resolve eq434200 eq428565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428565 eq434200
  have eq434325 : (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq434224 eq15
    | exact resolve eq15 eq434224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434340 : ∀ X0 : G, (k (k (σ y) (σ x)) X0) = (τ (k (σ (σ y)) (σ X0))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq434325 eq50
    | exact resolve eq50 eq434325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq434341 : ∀ X0 : G, (k X0 (k (σ y) (σ x))) = (τ (k (σ X0) (σ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq434325 eq55
    | exact resolve eq55 eq434325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq434325
  have eq434357 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq434341 X0
       have i₂ := eq48 X0 sF5
       grind)
    | exact superpose eq48 eq434341
    | exact resolve eq434341 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434341
  have eq434358 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ y) (σ x)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq434340 x
       have i₂ := eq48 sF5 x
       grind)
    | exact superpose eq48 eq434340
    | exact resolve eq434340 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434340
  have eq434635 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (k (k (σ y) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq434357 eq7416
    | exact resolve eq7416 eq434357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434712 : (k (σ (M.op x y)) (k (σ y) (σ x))) = (k (k (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq434357 eq322116
    | exact resolve eq322116 eq434357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322116 eq434357
  have eq434844 : (k (σ (M.op x y)) (k (σ y) (σ x))) = (k (k (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq434712
  have eq435268 : (k (k (σ y) (σ x)) (σ y)) = (k (σ y) (k (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq434358 eq263173
    | exact resolve eq263173 eq434358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263173
  have eq435336 : (k (k (σ y) (σ x)) (σ y)) = (k (σ y) (k (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq435268
  have eq436948 : (k (σ y) (σ (M.op x y))) = (k (σ y) (k (k (σ y) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq435336 eq288199
    | exact resolve eq288199 eq435336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288199 eq435336
  have eq436976 : (k (σ y) (σ (M.op x y))) = (k (σ y) (k (k (σ y) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq436948
  have eq437975 : (k (τ (σ y)) (M.op x y)) = (τ (k (σ y) (k (k (σ y) (σ x)) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq436976 eq76
    | exact resolve eq76 eq436976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq436976
  have eq438197 : (k (τ (σ y)) (M.op x y)) = (k (τ (σ y)) (τ (k (k (σ y) (σ x)) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq437975
       have i₂ := eq178 (k (k sF5 sF4) sF5) sF5
       grind)
    | exact superpose eq178 eq437975
    | exact resolve eq437975 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437975
  have eq438209 : (k (τ (σ y)) (M.op x y)) = (k (τ (σ y)) (k (τ (k (σ y) (σ x))) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq438197
       have i₂ := eq178 sF5 (k sF5 sF4)
       grind)
    | exact superpose eq178 eq438197
    | exact resolve eq438197 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438197
  have eq438214 : (k (τ (σ y)) (M.op x y)) = (k (τ (σ y)) (k (k (τ (σ y)) (τ (σ x))) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq438209
       have i₂ := eq178 sF4 sF5
       grind)
    | exact superpose eq178 eq438209
    | exact resolve eq438209 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438209
  have eq438641 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq434844 eq339369
    | exact resolve eq339369 eq434844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339369 eq434844
  have eq438735 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq438641
  have eq438872 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq438735 eq269437
    | exact resolve eq269437 eq438735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269437 eq438735
  have eq438912 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq438872
  have eq439222 : (k (σ y) (σ x)) ≠ (k (k (σ y) (σ y)) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq438912
  have eq444245 : (σ y) ≠ (k (k (σ y) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq434224 eq439222
    | exact resolve eq439222 eq434224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439222
  have eq444279 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq281869 eq444245
    | exact resolve eq444245 eq281869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281869 eq444245
  have eq444287 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq444279
  have eq446474 : (k (σ y) (σ x)) = (k (σ y) (k (k (σ y) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq434635 eq434358
    | exact resolve eq434358 eq434635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434635
  have eq446487 : (k (σ y) (σ x)) = (k (σ y) (k (k (σ y) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq446474
  have eq446525 : (τ (k (σ y) (σ x))) = (k (τ (σ y)) (τ (k (k (σ y) (σ x)) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq446487 eq178
    | exact resolve eq178 eq446487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446487
  have eq446538 : (τ (k (σ y) (σ x))) = (k (τ (σ y)) (k (τ (k (σ y) (σ x))) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq446525
       have i₂ := eq178 sF5 (k sF5 sF4)
       grind)
    | exact superpose eq178 eq446525
    | exact resolve eq446525 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446525
  have eq446545 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (k (k (τ (σ y)) (τ (σ x))) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq446538
       have i₂ := eq178 sF4 sF5
       grind)
    | exact superpose eq178 eq446538
    | exact resolve eq446538 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq446538
  have eq487419 : (k (τ (σ y)) (M.op x y)) = (k (k (τ (σ y)) (M.op x y)) (k (M.op x y) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq274885 eq326072
    | exact resolve eq326072 eq274885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274885 eq326072
  have eq487430 : (k (τ (σ y)) (M.op x y)) = (k (k (τ (σ y)) (M.op x y)) (k (M.op x y) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq487419
  have eq487491 : (σ (k (τ (σ y)) (M.op x y))) = (k (σ (k (τ (σ y)) (M.op x y))) (σ (k (M.op x y) (τ (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq487430 eq15
    | exact resolve eq15 eq487430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487430
  have eq487514 : (σ (k (τ (σ y)) (M.op x y))) = (k (σ (k (τ (σ y)) (M.op x y))) (k (σ (M.op x y)) (σ (τ (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq487491
       have i₂ := eq15 sF2 (τ sF5)
       grind)
    | exact superpose eq15 eq487491
    | exact resolve eq487491 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487491
  have eq487516 : (σ (k (τ (σ y)) (M.op x y))) = (k (σ (k (τ (σ y)) (M.op x y))) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq487514
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq487514
    | exact resolve eq487514 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487514
  have eq487517 : (σ (k (τ (σ y)) (M.op x y))) = (k (σ (k (τ (σ y)) (M.op x y))) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq487516
    | exact resolve eq487516 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487516
  have eq487518 : (k (σ (τ (σ y))) (σ (M.op x y))) = (k (k (σ (τ (σ y))) (σ (M.op x y))) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq487517
       have i₂ := eq15 (τ sF5) sF2
       grind)
    | exact superpose eq15 eq487517
    | exact resolve eq487517 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487517
  have eq487519 : (k (σ (τ (σ y))) (σ (M.op x y))) = (k (k (σ (τ (σ y))) (σ (M.op x y))) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq487518
    | exact resolve eq487518 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487518
  have eq487520 : (k (σ y) (σ (M.op x y))) = (k (k (σ y) (σ (M.op x y))) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq487519
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq487519
    | exact resolve eq487519 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487519
  have eq518705 : (k (σ y) (σ x)) ≠ (k (k (σ y) (σ y)) (k (k (k (σ y) (σ y)) (σ y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq327855
  have eq729338 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (k (k (σ y) (σ y)) (k (σ y) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq121117 eq221
    | exact resolve eq221 eq121117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121117
  have eq729344 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq729338 x
       have i₂ := eq221 (k sF5 sF5) x
       grind)
    | exact superpose eq221 eq729338
    | exact resolve eq729338 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq729338
  have eq729360 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq729344
  have eq751095 : (k (τ (σ y)) (M.op x y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq446545 eq438214
    | exact resolve eq438214 eq446545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438214 eq446545
  have eq751102 : (k (τ (σ y)) (M.op x y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq751095
  have eq751342 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (σ (k (τ (σ y)) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq751102 eq15
    | exact resolve eq15 eq751102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751102
  have eq751455 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq751342
       have i₂ := eq15 (τ sF5) sF2
       grind)
    | exact superpose eq15 eq751342
    | exact resolve eq751342 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751342
  have eq751456 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq751455
    | exact resolve eq751455 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751455
  have eq751457 : (k (σ y) (σ (M.op x y))) = (k (σ y) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq751456
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq751456
    | exact resolve eq751456 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751456
  have eq751458 : (k (σ y) (σ (M.op x y))) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq751457
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq751457
    | exact resolve eq751457 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751457
  have eq751766 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq751458 eq487520
    | exact resolve eq487520 eq751458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487520
  have eq751982 : (k (σ y) (σ x)) = (k (σ y) (k (k (σ y) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq751458 eq323310
    | exact resolve eq323310 eq751458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323310 eq751458
  have eq751994 : (k (σ y) (σ x)) = (k (σ y) (k (k (σ y) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq751982
  have eq752196 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq751766
  have eq754616 : (k (σ y) (σ x)) = (k (σ y) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq752196 eq434358
    | exact resolve eq434358 eq752196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434358 eq752196
  have eq754631 : (k (σ y) (σ x)) = (k (σ y) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq754616
  have eq805349 : ∀ X0 : G, (k X0 (σ (σ y))) = (τ (k (σ X0) (σ (σ (σ x))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq8748 eq48
    | exact resolve eq48 eq8748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8748
  have eq805358 : ∀ X0 : G, (k X0 (σ (σ y))) = (k X0 (σ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq805349 X0
       have i₂ := eq48 X0 (σ sF4)
       grind)
    | exact superpose eq48 eq805349
    | exact resolve eq805349 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805349
  have eq805385 : ∀ X0 : G, (k X0 (σ y)) = (τ (k (σ X0) (σ (σ x)))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq805358 eq48
    | exact resolve eq48 eq805358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805358
  have eq805397 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq805385 X0
       have i₂ := eq48 X0 sF4
       grind)
    | exact superpose eq48 eq805385
    | exact resolve eq805385 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq805385
  have eq805439 : (σ y) = (k (σ y) (k (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq805397 eq7416
    | exact resolve eq7416 eq805397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805397
  have eq805545 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq434224 eq805439
    | exact resolve eq805439 eq434224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434224 eq805439
  have eq805595 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq805545 eq33
    | exact resolve eq33 eq805545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805545
  have eq805597 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq805595
       have r₂ := eq261864
       grind)
    | exact resolve eq805595 eq261864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261864 eq805595
  have eq806248 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq805597 eq444287
    | (have r₁ := eq444287
       have r₂ := eq805597
       grind)
    | exact resolve eq444287 eq805597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444287
  have eq806442 : (k (σ y) (σ x)) ≠ (k (σ y) (k (k (σ y) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq805597 eq518705
    | exact resolve eq518705 eq805597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518705 eq805597
  have eq806984 : (k (σ y) (σ x)) ≠ (k (σ y) (k (k (σ y) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq806442
  have eq807178 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq806248
  have eq807179 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq807178
  have eq807844 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq806984
       have r₂ := eq751994
       grind)
    | exact resolve eq806984 eq751994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751994 eq806984
  have eq807945 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq807844 eq109611
    | (have r₁ := eq109611
       have r₂ := eq807844
       grind)
    | exact resolve eq109611 eq807844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109611 eq807844
  have eq807952 : (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq807945
  have eq808328 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq807179
  have eq819476 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq807952 eq808328
    | (have r₁ := eq808328
       have r₂ := eq807952
       grind)
    | exact resolve eq808328 eq807952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807952 eq808328
  have eq819493 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq819476
  have eq819494 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq819493
  have eq819523 : (σ y) = (σ (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq819494 eq35
    | exact resolve eq35 eq819494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819494
  have eq819532 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq819523
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq819523
    | exact resolve eq819523 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819523
  have eq819533 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq819532
  have eq819556 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq819533 eq6043
    | exact resolve eq6043 eq819533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6043
  have eq819575 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq819556
    | exact resolve eq819556 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819556
  have eq819584 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq819575 eq819533
    | exact resolve eq819533 eq819575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819533 eq819575
  have eq819585 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq819584
  have eq819694 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq819585 eq7466
    | exact resolve eq7466 eq819585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819585
  have eq820920 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq819694 eq729360
    | (have r₁ := eq729360
       have r₂ := eq819694
       grind)
    | exact resolve eq729360 eq819694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729360 eq819694
  have eq821013 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq820920
  have eq821014 : (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq821013
  have eq821302 : (σ y) = (σ (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq821014 eq35
    | exact resolve eq35 eq821014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821014
  have eq821317 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq821302
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq821302
    | exact resolve eq821302 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq821302
  have eq821318 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq821317
  have eq821320 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq821318 eq32
    | exact resolve eq32 eq821318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821411 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq821318 eq262398
    | exact resolve eq262398 eq821318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821318
  have eq826617 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq821411
  have eq826809 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq821320
       have i₂ := eq73 sF4
       grind)
    | exact superpose eq73 eq821320
    | exact resolve eq821320 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821320
  have eq826967 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq826809 eq33
    | exact resolve eq33 eq826809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826809
  have eq826992 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq826967
       have r₂ := eq826617
       grind)
    | exact resolve eq826967 eq826617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826617 eq826967
  have eq827091 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq826992 eq36
    | exact resolve eq36 eq826992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq833823 : (k (σ y) (σ x)) = (k (σ y) (k (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq826992 eq754631
    | exact resolve eq754631 eq826992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754631
  have eq834078 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq833823
       have i₂ := eq7416 sF5
       grind)
    | exact superpose eq7416 eq833823
    | exact resolve eq833823 eq7416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7416 eq833823
  have eq834079 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq834078
  have eq835727 : (M.op x y) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | exact superpose eq827091 eq42
    | exact resolve eq42 eq827091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq827091
  have eq842951 : (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | exact superpose eq835727 eq816
    | exact resolve eq816 eq835727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq842952 : (M.op x y) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq835727 eq842951
    | exact resolve eq842951 eq835727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835727 eq842951
  have eq844960 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq842952 eq7466
    | exact resolve eq7466 eq842952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7466 eq842952
  have eq845365 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq844960 eq15
    | exact resolve eq15 eq844960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844960
  have eq845381 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq845365
    | exact resolve eq845365 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq845365
  have eq845598 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq826992 eq845381
    | exact resolve eq845381 eq826992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845381
  have eq845910 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq845598 eq5987
    | exact resolve eq5987 eq845598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5987
  have eq851748 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq845910
       have r₂ := eq834079
       grind)
    | exact resolve eq845910 eq834079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845910
  have eq853499 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq834079 eq851748
    | exact resolve eq851748 eq834079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834079 eq851748
  have eq854818 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq853499 eq33
    | exact resolve eq33 eq853499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853499
  have eq854854 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq854818
       have r₂ := eq826992
       grind)
    | exact resolve eq854818 eq826992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826992 eq854818
  have eq854858 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq854854 eq32
    | exact resolve eq32 eq854854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq855000 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq854854 eq262398
    | exact resolve eq262398 eq854854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262398
  have eq860955 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq854854 eq845598
    | exact resolve eq845598 eq854854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845598 eq854854
  have eq860998 : (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq855000
  have eq866877 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq860955 eq860998
    | exact resolve eq860998 eq860955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860998
  have eq867000 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq854858
       have i₂ := eq73 sF4
       grind)
    | exact superpose eq73 eq854858
    | exact resolve eq854858 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq854858
  have eq872420 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq860955 eq867000
    | exact resolve eq867000 eq860955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860955 eq867000
  have eq903392 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq872420 eq33
    | exact resolve eq33 eq872420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq872420
  have eq903446 : False := by grind
  exact eq903446

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 (M.op (M.op X0 X1) X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X1) (M.op X2 (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq9 X1 (M.op X2 (M.op (M.op X0 X1) X1)) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq14 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85
    | (have j0 := eq85 (σ X0) (σ X1)
       grind)
    | exact resolve eq85 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq116 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq107 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq107 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq144 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq153 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq144 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq157 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq153 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq153
    | exact resolve eq153 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq157 X0
       have i₂ := eq153 X0
       grind)
    | exact superpose eq153 eq157
    | exact resolve eq157 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq157
  have eq349 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq160 X1
       grind)
    | exact superpose eq160 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq514 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq349 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq349 X0 X1
       grind)
    | exact superpose eq349 eq10
    | (have j1 := eq349 X0 X1
       grind)
    | exact resolve eq10 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq553 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq514
    | (have j0 := eq514 X0 X1
       grind)
    | exact resolve eq514 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq612 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq553 y x
       grind)
    | exact superpose eq553 eq16
    | (have j1 := eq553 y x
       grind)
    | exact resolve eq16 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq632 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq612
       have i₂ := eq85 y x
       grind)
    | exact superpose eq85 eq612
    | (have j1 := eq85 y x
       grind)
    | exact resolve eq612 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq612
  have eq634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq632
  have eq635 : y = (M.op x x) := by grind
  clear eq634
  have eq697 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 X2 X1 X0
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq855 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq697 x X2 X0
       have i₂ := eq697 x X2 X3
       grind)
    | exact superpose eq697 eq697
    | exact resolve eq697 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X2 x
       have i₂ := eq697 x X2 X0
       grind)
    | exact superpose eq697 eq9
    | exact resolve eq9 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq927 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq871 x x
       have i₂ := eq635
       grind)
    | exact superpose eq635 eq871
    | exact resolve eq871 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq871 X0 (M.op X0 X0)
       have i₂ := eq871 X0 X0
       grind)
    | exact superpose eq871 eq871
    | exact resolve eq871 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : y = (M.op y x) := by
    first
    | (have i₁ := eq871 x y
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq871
    | exact resolve eq871 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq960 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op x y) X0 x
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq9
    | exact resolve eq9 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq960 X0
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq960
    | exact resolve eq960 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq960
  have eq1253 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0 x
       have i₂ := eq937 X0
       grind)
    | exact superpose eq937 eq31
    | exact resolve eq31 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1255 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq937 X0
       grind)
    | exact superpose eq937 eq9
    | exact resolve eq9 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq1327 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1255 (σ X0) X1
       have i₂ := eq160 X0
       grind)
    | exact superpose eq160 eq1255
    | exact resolve eq1255 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1606 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq976 y
       have i₂ := eq958
       grind)
    | exact superpose eq958 eq976
    | exact resolve eq976 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq976
  have eq3345 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1253 X0 X0
       have i₂ := eq855 X1 X0 X0
       grind)
    | (have i₁ := eq1253 X0 X0
       have i₂ := eq855 X0 X0 X1
       grind)
    | exact superpose eq855 eq1253
    | exact resolve eq1253 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq1253
  have eq3701 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1327 x X0
       have i₂ := eq635
       grind)
    | exact superpose eq635 eq1327
    | exact resolve eq1327 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq1327
  have eq4871 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3345 (σ y) x
       have i₂ := eq3701 x
       grind)
    | exact superpose eq3701 eq3345
    | exact resolve eq3345 eq3701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345 eq3701
  have eq4908 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4871
       have i₂ := eq160 y
       grind)
    | exact superpose eq160 eq4871
    | exact resolve eq4871 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq4871
  have eq4937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4908
       have i₂ := eq1606
       grind)
    | exact superpose eq1606 eq4908
    | exact resolve eq4908 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606 eq4908
  have eq4949 : False := by grind
  exact eq4949

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
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
  clear eq25
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23 eq37
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq605 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq810 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq605 X1 x X3
       have i₂ := eq605 X1 x X0
       grind)
    | exact superpose eq605 eq605
    | exact resolve eq605 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq605 X1 x X0
       grind)
    | exact superpose eq605 eq14
    | exact resolve eq14 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq857 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq822 X0 (M.op X0 X0)
       have i₂ := eq822 X0 X0
       grind)
    | exact superpose eq822 eq822
    | exact resolve eq822 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq857 X0
       grind)
    | exact superpose eq857 eq14
    | exact resolve eq14 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq1409 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq810 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq822 X1 X0
       grind)
    | exact superpose eq822 eq810
    | exact resolve eq810 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq822
  have eq23134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23134
    | exact resolve eq23134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23134
  have eq23146 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23135
       have r₂ := eq28
       grind)
    | exact resolve eq23135 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23135
  have eq23160 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq23146 eq1409
    | exact resolve eq1409 eq23146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23146
  have eq23168 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23160 x
       have i₂ := eq964 sF3 x
       grind)
    | exact superpose eq964 eq23160
    | exact resolve eq23160 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23160
  have eq23169 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23168
  have eq23175 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23169
  have eq23229 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23175
    | exact resolve eq23175 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23175
  have eq23971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23229 eq96
    | exact resolve eq96 eq23229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq23229
  have eq23983 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23971
  have eq23985 : y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23983
       have r₂ := eq28
       grind)
    | exact resolve eq23983 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23983
  have eq23999 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 (M.op y y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1409 x y X0
       have i₂ := eq23985
       grind)
    | exact superpose eq23985 eq1409
    | exact resolve eq1409 eq23985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23985
  have eq24007 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23999 x
       have i₂ := eq964 y x
       grind)
    | exact superpose eq964 eq23999
    | exact resolve eq23999 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23999
  have eq24008 : y = (M.op x x) := by grind
  clear eq24007
  have eq24014 : (M.op x y) = (k y x) := by grind
  clear eq24008
  have eq24068 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq24014
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24014
    | exact resolve eq24014 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24014
  have eq24988 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq24068
       grind)
    | exact superpose eq24068 eq70
    | exact resolve eq70 eq24068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq24068
  have eq25014 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq24988
    | exact resolve eq24988 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq24988
  have eq25495 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25014 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq25014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq25495
    | exact resolve eq25495 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25495
  have eq25507 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq25496
       have r₂ := eq28
       grind)
    | exact resolve eq25496 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25496
  have eq35567 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq25507 eq1409
    | exact resolve eq1409 eq25507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq25507
  have eq35575 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35567 x
       have i₂ := eq964 sF3 x
       grind)
    | exact superpose eq964 eq35567
    | exact resolve eq35567 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq35567
  have eq35576 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq35575
  have eq35957 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq35576
  have eq36011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25014 eq35957
    | exact resolve eq35957 eq25014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25014 eq35957
  have eq36019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq36011
    | exact resolve eq36011 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq36011
  have eq36020 : False := by grind
  exact eq36020

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxx_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op (k (M.op X0 X0) X0) (M.op X0 X0)))) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
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
  have eq77 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq78 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq215 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op X0 (M.op X0 (M.op (σ y) (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq232 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq278 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq16
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq401 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq232
    | exact resolve eq232 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq232 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq232
    | (have j0 := eq232 X0 y
       grind)
    | exact resolve eq232 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq485 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq733 : ∀ X0 : G, (σ (k (k y y) X0)) = (M.op (σ X0) (k (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (k (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (k y y) x
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq94
    | exact resolve eq94 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq954 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq627 X1 x X3
       have i₂ := eq627 X1 x X0
       grind)
    | exact superpose eq627 eq627
    | exact resolve eq627 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq627 X1 x X0
       grind)
    | exact superpose eq627 eq14
    | exact resolve eq14 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 (M.op X2 X0) X2
       have i₂ := eq627 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq627 eq54
    | exact resolve eq54 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq989 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq981 X0 X1 X2
       have i₂ := eq54 X0 X0 X1
       grind)
    | exact superpose eq54 eq981
    | exact resolve eq981 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1005 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq968 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq968
    | (have j0 := eq968 x y
       grind)
    | exact resolve eq968 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq968
    | (have j0 := eq968 (σ x) (σ y)
       grind)
    | exact resolve eq968 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1012 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq968 X0 (M.op X0 X0)
       have i₂ := eq968 X0 X0
       grind)
    | exact superpose eq968 eq968
    | exact resolve eq968 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1019 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq968 X0 X1
       grind)
    | exact superpose eq968 eq54
    | exact resolve eq54 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1024 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1019 X1 X0 X2
       have i₂ := eq968 X0 X1
       grind)
    | exact superpose eq968 eq1019
    | exact resolve eq1019 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1031 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 (M.op y (M.op x (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq1005 eq14
    | exact resolve eq14 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1005 eq1031
    | exact resolve eq1031 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1045 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq1006 eq14
    | exact resolve eq14 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1006 eq54
    | exact resolve eq54 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1053 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1006 eq1047
    | exact resolve eq1047 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1055 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1006 eq1045
    | exact resolve eq1045 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1133 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq1012 X0
       grind)
    | exact superpose eq1012 eq14
    | exact resolve eq14 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1239 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq1041 (M.op y y)
       have i₂ := eq1012 y
       grind)
    | exact superpose eq1012 eq1041
    | exact resolve eq1041 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1259 : (M.op x (M.op x y)) = (k (M.op y y) y) := by grind
  clear eq1239
  have eq1306 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq1053
    | (have j0 := eq1053 (σ x)
       grind)
    | exact resolve eq1053 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1337 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq1055 (M.op sF3 sF3)
       have i₂ := eq1012 sF3
       grind)
    | exact superpose eq1012 eq1055
    | exact resolve eq1055 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ y) (σ y)) (σ y)) := by grind
  clear eq1337
  have eq1750 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    grind
  have eq1863 : ∀ X0 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1750 X0 x
       have i₂ := eq1133 X0 x
       grind)
    | exact superpose eq1133 eq1750
    | exact resolve eq1750 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1952 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq989 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq989
    | (have j0 := eq989 y X0 x
       grind)
    | exact resolve eq989 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1956 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq989
    | (have j0 := eq989 (σ y) X0 (σ x)
       grind)
    | exact resolve eq989 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1960 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1 X0
       have i₂ := eq1012 X0
       grind)
    | exact superpose eq1012 eq989
    | exact resolve eq989 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2097 : (M.op (M.op x y) y) = (M.op y y) := by
    first
    | (have i₁ := eq1952 y
       have i₂ := eq1012 y
       grind)
    | exact superpose eq1012 eq1952
    | exact resolve eq1952 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2118 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op X1 y) (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq954 X0 y (M.op X1 y)
       have i₂ := eq1952 X1
       grind)
    | (have i₁ := eq954 X0 y (M.op x y)
       have i₂ := eq1952 X0
       grind)
    | exact superpose eq1952 eq954
    | exact resolve eq954 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq2122 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op X1 y) (M.op (M.op x y) y)) := by
    intro X1
    first
    | (have i₁ := eq2118 x X1
       have i₂ := eq1041 x
       grind)
    | (have i₁ := eq2118 x X1
       have i₂ := eq1041 x
       grind)
    | exact superpose eq1041 eq2118
    | (have j0 := eq2118 x X1
       grind)
    | exact resolve eq2118 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2204 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1956 sF3
       have i₂ := eq1012 sF3
       grind)
    | exact superpose eq1012 eq1956
    | exact resolve eq1956 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq2225 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op X1 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1956 eq954
    | exact resolve eq954 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq2229 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X1 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X1
    first
    | exact superpose eq1055 eq2225
    | (have j0 := eq2225 (σ x) X1
       grind)
    | exact resolve eq2225 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq2385 : (M.op y (M.op x (M.op x y))) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq1005 eq1960
    | exact resolve eq1960 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2390 : (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1006 eq1960
    | exact resolve eq1960 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2449 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1006 eq2390
    | exact resolve eq2390 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390
  have eq2452 : y = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq1005 eq2385
    | exact resolve eq2385 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2385
  have eq3089 : (M.op y y) = (k y (M.op x (M.op x y))) := by grind
  have eq3122 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (σ y))) = (M.op X0 (M.op X0 (M.op (σ y) (M.op X1 (M.op (σ y) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq2204 eq215
    | exact resolve eq215 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq3494 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (k (M.op (σ y) (σ y)) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq3122 sF3 (k (M.op sF3 sF3) sF3)
       have i₂ := eq65 sF3 sF3
       grind)
    | exact superpose eq65 eq3122
    | exact resolve eq3122 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq3122
  have eq3546 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1357 eq3494
    | exact resolve eq3494 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3494
  have eq3560 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1055 eq3546
    | exact resolve eq3546 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3546
  have eq3571 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3560 eq14
    | exact resolve eq14 eq3560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3596 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3560 eq3571
    | exact resolve eq3571 eq3560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3571
  have eq3841 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 X1 X1
       have i₂ := eq1960 X0 X1
       grind)
    | exact superpose eq1960 eq485
    | exact resolve eq485 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq3842 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3841 X0 x
       have i₂ := eq1960 (M.op X0 X0) x
       grind)
    | exact superpose eq1960 eq3841
    | exact resolve eq3841 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3841
  have eq3843 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq3842
  have eq3844 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq3873 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3844 X0
       have i₂ := eq1863 X0
       grind)
    | exact superpose eq1863 eq3844
    | exact resolve eq3844 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863 eq3844
  have eq3876 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3873 X0
       have i₂ := eq3843 X0
       grind)
    | exact superpose eq3843 eq3873
    | exact resolve eq3873 eq3843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3873
  have eq3877 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3876 X1
       have i₂ := eq954 X1 X1 X0
       grind)
    | (have i₁ := eq3876 X1
       have i₂ := eq954 X0 X1 X1
       grind)
    | exact superpose eq954 eq3876
    | exact resolve eq3876 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3889 : y = (k (M.op x (M.op x y)) (M.op y y)) := by
    first
    | (have i₁ := eq3876 y
       have i₂ := eq1041 y
       grind)
    | exact superpose eq1041 eq3876
    | exact resolve eq3876 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3890 : (σ y) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1055 eq3876
    | exact resolve eq3876 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq3891 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq3876
  have eq3902 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3891 X0
       have i₂ := eq3843 X0
       grind)
    | exact superpose eq3843 eq3891
    | exact resolve eq3891 eq3843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891
  have eq3914 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3902 X0
       have i₂ := eq1024 X0 X0 X0
       grind)
    | exact superpose eq1024 eq3902
    | exact resolve eq3902 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3902
  have eq4222 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3914 X1
       have i₂ := eq954 X1 X1 X0
       grind)
    | (have i₁ := eq3914 X1
       have i₂ := eq954 X0 X1 X1
       grind)
    | exact superpose eq954 eq3914
    | exact resolve eq3914 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3914
  have eq4694 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op X1 y) (M.op y y)) := by
    intro X1
    first
    | exact superpose eq2097 eq2122
    | exact resolve eq2122 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097 eq2122
  have eq4776 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X1 (σ y)) (M.op (σ y) (σ y))) := by
    intro X1
    first
    | exact superpose eq2204 eq2229
    | exact resolve eq2229 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204 eq2229
  have eq19522 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19522
    | exact resolve eq19522 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19522
  have eq19534 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19523
       have r₂ := eq28
       grind)
    | exact resolve eq19523 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19523
  have eq19536 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19534
    | exact resolve eq19534 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19534
  have eq19548 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19536 eq3843
    | exact resolve eq3843 eq19536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19536
  have eq19600 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19548
    | exact resolve eq19548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19548
  have eq20024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19600 eq114
    | exact resolve eq114 eq19600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19600
  have eq20037 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20024
  have eq20039 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20037
       have r₂ := eq28
       grind)
    | exact resolve eq20037 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20037
  have eq20052 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3843 x
       have i₂ := eq20039
       grind)
    | exact superpose eq20039 eq3843
    | exact resolve eq3843 eq20039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20039
  have eq20104 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20052
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20052
    | exact resolve eq20052 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20052
  have eq20652 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq20104
       grind)
    | exact superpose eq20104 eq72
    | exact resolve eq72 eq20104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20104
  have eq20676 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq20652
    | exact resolve eq20652 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20652
  have eq20926 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20676 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq20676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq20926
    | exact resolve eq20926 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20926
  have eq20940 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20929
       have r₂ := eq28
       grind)
    | exact resolve eq20929 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20929
  have eq20942 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq20940
    | exact resolve eq20940 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20940
  have eq20943 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20942
  have eq20996 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20943 eq3843
    | exact resolve eq3843 eq20943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843 eq20943
  have eq21048 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq20996
    | exact resolve eq20996 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20996
  have eq21238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21048 eq20676
    | exact resolve eq20676 eq21048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20676 eq21048
  have eq21245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21238
  have eq21249 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21245
       have r₂ := eq28
       grind)
    | exact resolve eq21245 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21245
  have eq21251 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21249 eq28
    | exact resolve eq28 eq21249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21253 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21249 eq78
    | (have r₁ := eq78
       have r₂ := eq21249
       grind)
    | exact resolve eq78 eq21249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq21258 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21249 eq1306
    | exact resolve eq1306 eq21249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21262 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21249 eq2449
    | exact resolve eq2449 eq21249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq21265 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21249 eq3560
    | exact resolve eq3560 eq21249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3560
  have eq21269 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21249 eq3890
    | exact resolve eq3890 eq21249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3890
  have eq21271 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq21253
  have eq21272 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq21269
    | exact resolve eq21269 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21269
  have eq21276 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4776 eq21265
    | exact resolve eq21265 eq4776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4776 eq21265
  have eq21279 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq21262
    | exact resolve eq21262 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21262
  have eq21282 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq21258
    | exact resolve eq21258 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21258
  have eq21285 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq21276
    | exact resolve eq21276 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21276
  have eq21289 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21249 eq21279
    | exact resolve eq21279 eq21249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21330 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21279 eq989
    | exact resolve eq989 eq21279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq21279
  have eq21338 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21289
  have eq21344 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21330 x
       have i₂ := eq1960 sF4 x
       grind)
    | exact superpose eq1960 eq21330
    | exact resolve eq21330 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21330
  have eq21420 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21285 eq954
    | exact resolve eq954 eq21285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21285
  have eq21504 : (σ y) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21338 eq3877
    | exact resolve eq3877 eq21338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21508 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1357 eq21504
    | exact resolve eq21504 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21504
  have eq21561 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21508 eq954
    | exact resolve eq954 eq21508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21508
  have eq21585 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27 eq21561
    | (have j0 := eq21561 X0
       grind)
    | exact resolve eq21561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21561
  have eq21662 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21338 eq21272
    | exact resolve eq21272 eq21338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21272 eq21338
  have eq21670 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21662
  have eq21677 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21249 eq21670
    | exact resolve eq21670 eq21249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21670
  have eq21693 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21677
  have eq21699 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21693 eq88
    | exact resolve eq88 eq21693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21693
  have eq21742 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq21699
    | exact resolve eq21699 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21699
  have eq21768 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq21742
       grind)
    | exact superpose eq21742 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq21742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21769 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq21768
  have eq21804 : (k y y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1259
       have i₂ := eq21769
       grind)
    | exact superpose eq21769 eq1259
    | exact resolve eq1259 eq21769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21818 : (M.op y y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4694 y
       have i₂ := eq21769
       grind)
    | exact superpose eq21769 eq4694
    | exact resolve eq4694 eq21769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4694
  have eq21823 : (k y y) = (M.op y y) ∨ y = (M.op x y) := by grind
  have eq21866 : y = (k (M.op y y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3877 y y
       have i₂ := eq21769
       grind)
    | exact superpose eq21769 eq3877
    | exact resolve eq3877 eq21769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21769
  have eq21872 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21866
       have i₂ := eq1259
       grind)
    | exact superpose eq1259 eq21866
    | exact resolve eq21866 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21866
  have eq22048 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21872 eq954
    | exact resolve eq954 eq21872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22052 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 (M.op X0 (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21872 eq1024
    | exact resolve eq1024 eq21872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21872
  have eq22067 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22048 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22048
    | (have j0 := eq22048 X0
       grind)
    | exact resolve eq22048 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22048
  have eq25055 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21282 eq21585
    | exact resolve eq21585 eq21282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21282 eq21585
  have eq25116 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq25055
  have eq25157 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25116 eq1357
    | exact resolve eq1357 eq25116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357 eq25116
  have eq25485 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21249 eq25157
    | exact resolve eq25157 eq21249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25157
  have eq25509 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq25485
  have eq25510 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq25509
    | exact resolve eq25509 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25509
  have eq25519 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25510 eq88
    | exact resolve eq88 eq25510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq25510
  have eq25578 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21742
       have i₂ := eq25519
       grind)
    | exact superpose eq25519 eq21742
    | exact resolve eq21742 eq25519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21742
  have eq25596 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq25578
  have eq25674 : ∀ X0 : G, (k y (τ X0)) = (τ (k (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25596 eq401
    | exact resolve eq401 eq25596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq25596
  have eq25697 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25674 X0
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq25674
    | exact resolve eq25674 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq25674
  have eq27471 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25519
       have i₂ := eq21804
       grind)
    | exact superpose eq21804 eq25519
    | exact resolve eq25519 eq21804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21804
  have eq27489 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq27471
  have eq27526 : y = (k (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27489 eq3889
    | exact resolve eq3889 eq27489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq27544 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27489 eq1960
    | exact resolve eq1960 eq27489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27489
  have eq29148 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25519
       have i₂ := eq21823
       grind)
    | exact superpose eq21823 eq25519
    | exact resolve eq25519 eq21823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21823 eq25519
  have eq29164 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq29148
  have eq29199 : (M.op x (M.op x y)) = (k (τ (M.op (σ x) (σ y))) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1259
       have i₂ := eq29164
       grind)
    | exact superpose eq29164 eq1259
    | exact resolve eq1259 eq29164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259 eq29164
  have eq29290 : (M.op x (M.op x y)) = (τ (k (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29199
       have i₂ := eq417 sF4
       grind)
    | exact superpose eq417 eq29199
    | exact resolve eq29199 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq29199
  have eq38628 : y = (k (τ (M.op (σ x) (σ y))) (M.op x (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27526
       have i₂ := eq21818
       grind)
    | exact superpose eq21818 eq27526
    | exact resolve eq27526 eq21818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27526
  have eq38659 : y = (k (τ (M.op (σ x) (σ y))) (M.op x (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq38628
  have eq39104 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27544 eq22067
    | exact resolve eq22067 eq27544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22067 eq27544
  have eq39127 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq39104
  have eq41319 : (σ (M.op x (M.op x y))) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29290 eq15
    | exact resolve eq15 eq29290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29290
  have eq43951 : (σ y) = (k (M.op (σ x) (σ y)) (σ (M.op x (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38659 eq35
    | exact resolve eq35 eq38659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq38659
  have eq44032 : (σ y) = (k (M.op (σ x) (σ y)) (σ (M.op x (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43951
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq43951
    | exact resolve eq43951 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43951
  have eq45441 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39127 eq1133
    | exact resolve eq1133 eq39127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39127
  have eq49833 : (σ y) = (k (σ y) (σ (M.op x (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21249 eq44032
    | exact resolve eq44032 eq21249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21249
  have eq49837 : (σ y) = (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41319 eq44032
    | exact resolve eq44032 eq41319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41319 eq44032
  have eq49859 : (σ y) = (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq49837
  have eq49863 : (σ y) = (k (σ y) (σ (M.op x (M.op x y)))) ∨ y = (M.op x y) := by grind
  clear eq49833
  have eq49875 : (σ y) = (σ (k y (M.op x (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq49863
    | exact resolve eq49863 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq49863
  have eq49876 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3089 eq49875
    | exact resolve eq49875 eq3089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089 eq49875
  have eq49878 : (σ y) = (σ (M.op x (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq49876
       have i₂ := eq21818
       grind)
    | exact superpose eq21818 eq49876
    | exact resolve eq49876 eq21818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21818 eq49876
  have eq49966 : (σ y) = (σ (M.op x (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq49878
  have eq63389 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21344 eq21420
    | exact resolve eq21420 eq21344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21420
  have eq63474 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by grind
  clear eq63389
  have eq68222 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (M.op X0 (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq63474 eq954
    | exact resolve eq954 eq63474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63474
  have eq68255 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1306 eq68222
    | exact resolve eq68222 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68222
  have eq70950 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq68255 sF3
       have i₂ := eq954 sF3 sF4 x
       grind)
    | (have i₁ := eq68255 sF3
       have i₂ := eq954 X0 sF4 sF3
       grind)
    | exact superpose eq954 eq68255
    | exact resolve eq68255 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq68255
  have eq75746 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21344 eq70950
    | exact resolve eq70950 eq21344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21344 eq70950
  have eq75805 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x y) := by grind
  clear eq75746
  have eq93690 : (M.op x y) = (M.op y (M.op (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq45441 eq22052
    | exact resolve eq22052 eq45441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22052 eq45441
  have eq93746 : (M.op x y) = (M.op y (M.op (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq93690
  have eq125680 : (τ (σ y)) = (τ (k (σ y) (k (M.op (σ x) (σ y)) (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49859 eq25697
    | exact resolve eq25697 eq49859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25697 eq49859
  have eq125958 : (τ (σ y)) = (τ (k (σ y) (k (M.op (σ x) (σ y)) (σ y)))) ∨ y = (M.op x y) := by grind
  clear eq125680
  have eq126208 : y = (τ (k (σ y) (k (M.op (σ x) (σ y)) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq125958
    | exact resolve eq125958 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq125958
  have eq289094 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21271 eq114
    | exact resolve eq114 eq21271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq21271
  have eq289137 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq289094
  have eq289153 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq289137
       have r₂ := eq21251
       grind)
    | exact resolve eq289137 eq21251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21251 eq289137
  have eq289491 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq289153 eq3877
    | exact resolve eq3877 eq289153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289153
  have eq289502 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq289491
    | exact resolve eq289491 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289491
  have eq290820 : y = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq289502 eq126208
    | exact resolve eq126208 eq289502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126208 eq289502
  have eq290884 : y = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq290820
  have eq290958 : y = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq83 eq290884
    | exact resolve eq290884 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq290884
  have eq290980 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq290958
       have r₂ := eq77
       grind)
    | exact resolve eq290958 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq290958
  have eq290984 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq290980
       grind)
    | exact superpose eq290980 eq72
    | exact resolve eq72 eq290980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291009 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq290980
       grind)
    | exact superpose eq290980 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq290980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290980
  have eq291020 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq291009
  have eq291031 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq291020
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq291020
    | exact resolve eq291020 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291020
  have eq291054 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq290984
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq290984
    | exact resolve eq290984 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290984
  have eq291569 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq968 x x
       have i₂ := eq291031
       grind)
    | exact superpose eq291031 eq968
    | exact resolve eq968 eq291031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291031
  have eq291593 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq291569
       have i₂ := eq1041 x
       grind)
    | (have i₁ := eq291569
       have i₂ := eq1041 x
       grind)
    | exact superpose eq1041 eq291569
    | exact resolve eq291569 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq291569
  have eq293327 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq291593 eq49966
    | exact resolve eq49966 eq291593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49966 eq291593
  have eq293384 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq293327
  have eq293414 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq293384
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq293384
    | exact resolve eq293384 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293384
  have eq294606 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq293414 eq75805
    | exact resolve eq75805 eq293414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75805 eq293414
  have eq295113 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ y = (M.op x y) := by grind
  clear eq294606
  have eq295368 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1306 eq295113
    | exact resolve eq295113 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306 eq295113
  have eq295454 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq295368
    | exact resolve eq295368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295368
  have eq297013 : (M.op x y) = (M.op y (M.op (τ (σ x)) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq295454 eq93746
    | exact resolve eq93746 eq295454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93746 eq295454
  have eq297486 : (M.op x y) = (M.op y (M.op (τ (σ x)) (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq297013
  have eq297933 : (M.op x y) = (M.op y (M.op x (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq297486
    | exact resolve eq297486 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297486
  have eq298029 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1005 eq297933
    | exact resolve eq297933 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq297933
  have eq298030 : y = (M.op x y) := by grind
  clear eq298029
  have eq298059 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq298030 eq21
    | exact resolve eq21 eq298030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq298187 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq298030 eq2452
    | exact resolve eq2452 eq298030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2452
  have eq298298 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq298187
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq298187
    | exact resolve eq298187 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298187
  have eq298413 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq298059
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq298059
    | exact resolve eq298059 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298059
  have eq298423 : y = (M.op y y) := by
    first
    | exact superpose eq298030 eq298298
    | exact resolve eq298298 eq298030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298298
  have eq298446 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq298413 eq27
    | exact resolve eq27 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq298513 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq298413 eq1006
    | exact resolve eq1006 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq299287 : y = (k y (M.op y y)) := by
    first
    | (have i₁ := eq4222 y y
       have i₂ := eq298423
       grind)
    | exact superpose eq298423 eq4222
    | exact resolve eq4222 eq298423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4222
  have eq299302 : y = (k y y) := by
    first
    | (have i₁ := eq299287
       have i₂ := eq298423
       grind)
    | exact superpose eq298423 eq299287
    | exact resolve eq299287 eq298423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298423 eq299287
  have eq301450 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq299302
       grind)
    | exact superpose eq299302 eq73
    | exact resolve eq73 eq299302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq301510 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq749 y y
       have i₂ := eq299302
       grind)
    | exact superpose eq299302 eq749
    | (have j0 := eq749 y y
       grind)
    | exact resolve eq749 eq299302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq301518 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq301510
  have eq301519 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq301518
  have eq301536 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq301519
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq301519
    | exact resolve eq301519 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301519
  have eq301565 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq298413 eq301450
    | exact resolve eq301450 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301450
  have eq301567 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq298413 eq301536
    | exact resolve eq301536 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301536
  have eq301594 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq301565
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq301565
    | exact resolve eq301565 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301565
  have eq301618 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq298413 eq301594
    | exact resolve eq301594 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301594
  have eq302772 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq301567 eq1133
    | exact resolve eq1133 eq301567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq304273 : ∀ X0 : G, (σ (k (k y y) X0)) = (M.op (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (k (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq298413 eq733
    | (have j0 := eq733 X0
       grind)
    | exact resolve eq733 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq304274 : ∀ X0 : G, (σ (k (k y y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (k (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq301618 eq304273
    | (have j0 := eq304273 X0
       grind)
    | exact resolve eq304273 eq301618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304273
  have eq304275 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (k (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq304274 X0
       have i₂ := eq299302
       grind)
    | exact superpose eq299302 eq304274
    | (have j0 := eq304274 X0
       grind)
    | exact resolve eq304274 eq299302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304274
  have eq304276 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq298413 eq304275
    | (have j0 := eq304275 X0
       grind)
    | exact resolve eq304275 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304275
  have eq304277 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq301618 eq304276
    | (have j0 := eq304276 X0
       grind)
    | exact resolve eq304276 eq301618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304276
  have eq304278 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq298413 eq304277
    | (have j0 := eq304277 X0
       grind)
    | exact resolve eq304277 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304277
  have eq304279 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq301618 eq304278
    | (have j0 := eq304278 X0
       grind)
    | exact resolve eq304278 eq301618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301618 eq304278
  have eq304643 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq304279 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq304279
    | (have j0 := eq304279 x
       grind)
    | exact resolve eq304279 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304279
  have eq304723 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq298446 eq304643
    | exact resolve eq304643 eq298446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304643
  have eq304967 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq304723
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq304723
    | exact resolve eq304723 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq304723
  have eq305138 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq298413 eq304967
    | exact resolve eq304967 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304967
  have eq305289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq298446 eq305138
    | exact resolve eq305138 eq298446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305138
  have eq305372 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq305289
       have r₂ := eq28
       grind)
    | exact resolve eq305289 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305289
  have eq305633 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq298513 eq1024
    | exact resolve eq1024 eq298513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024 eq298513
  have eq305660 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3596 eq305633
    | exact resolve eq305633 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596 eq305633
  have eq305685 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq298413 eq305660
    | exact resolve eq305660 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305660
  have eq305696 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq301567 eq305685
    | exact resolve eq305685 eq301567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305685
  have eq305704 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq301567 eq305696
    | exact resolve eq305696 eq301567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301567 eq305696
  have eq305837 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq305704 eq968
    | exact resolve eq968 eq305704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305842 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq305704 eq1960
    | exact resolve eq1960 eq305704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq305862 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq298446 eq305837
    | exact resolve eq305837 eq298446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298446 eq305837
  have eq322597 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq305862 eq305842
    | exact resolve eq305842 eq305862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305842 eq305862
  have eq374472 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq298413 eq291054
    | exact resolve eq291054 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291054
  have eq374490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq374472 eq305372
    | exact resolve eq305372 eq374472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305372 eq374472
  have eq374516 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq374490
       have r₂ := eq28
       grind)
    | exact resolve eq374490 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374490
  have eq380017 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq374516 eq968
    | exact resolve eq968 eq374516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq374516
  have eq380050 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq302772 eq380017
    | exact resolve eq380017 eq302772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302772 eq380017
  have eq380157 : x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3877 x x
       have i₂ := eq380050
       grind)
    | exact superpose eq380050 eq3877
    | exact resolve eq3877 eq380050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3877 eq380050
  have eq380173 : x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq380157
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq380157
    | exact resolve eq380157 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq380157
  have eq380211 : x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq298030 eq380173
    | exact resolve eq380173 eq298030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380173
  have eq380244 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq380211
       have i₂ := eq299302
       grind)
    | exact superpose eq299302 eq380211
    | exact resolve eq380211 eq299302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299302 eq380211
  have eq380291 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq380244 eq29
    | exact resolve eq29 eq380244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq380244
  have eq380653 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq380291
    | exact resolve eq380291 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq380291
  have eq380751 : x = y ∨ x = y := by
    first
    | exact superpose eq298030 eq380653
    | exact resolve eq380653 eq298030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298030 eq380653
  have eq380752 : x = y := by grind
  clear eq380751
  have eq380898 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq380752
       grind)
    | exact superpose eq380752 eq25
    | exact resolve eq25 eq380752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq380752
  have eq381615 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq298413 eq380898
    | exact resolve eq380898 eq298413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298413 eq380898
  have eq381902 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq381615
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq381615
    | exact resolve eq381615 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq381615
  have eq385361 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq381902 eq305704
    | exact resolve eq305704 eq381902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305704 eq381902
  have eq385373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq322597 eq385361
    | exact resolve eq385361 eq322597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322597 eq385361
  have eq385474 : False := by grind
  exact eq385474

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq143 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq136
    | (have j0 := eq136 X0 X1
       grind)
    | exact resolve eq136 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq441 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op X2 (M.op X2 (M.op (σ X0) (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 (σ X0) X1 X2 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq104
    | exact resolve eq104 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq104
    | exact resolve eq104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq465 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq448 X1 x X3
       have i₂ := eq448 X1 x X0
       grind)
    | exact superpose eq448 eq448
    | exact resolve eq448 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq448 X1 x X0
       grind)
    | exact superpose eq448 eq9
    | exact resolve eq9 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X0 (M.op X2 X0) X2
       have i₂ := eq448 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq448 eq105
    | exact resolve eq105 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq490 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq483 X0 X1 X2
       have i₂ := eq105 X0 X0 X1
       grind)
    | exact superpose eq105 eq483
    | exact resolve eq483 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq506 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq474 X0 (M.op X0 X0)
       have i₂ := eq474 X0 X0
       grind)
    | exact superpose eq474 eq474
    | exact resolve eq474 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq474 X0 X1
       grind)
    | exact superpose eq474 eq105
    | exact resolve eq105 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq515 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq512 X1 X0 X2
       have i₂ := eq474 X0 X1
       grind)
    | exact superpose eq474 eq512
    | exact resolve eq512 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq519 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq506 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq506
    | exact resolve eq506 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq9
    | exact resolve eq9 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq524 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq524
    | exact resolve eq524 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq563 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq465 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq474 X1 X0
       grind)
    | exact superpose eq474 eq465
    | exact resolve eq465 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq668 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq490 X0 X1 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq490
    | exact resolve eq490 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq490 (M.op X2 (M.op X2 X0)) (M.op x X0) X1
       have i₂ := eq515 X0 X2 x
       grind)
    | exact superpose eq515 eq490
    | exact resolve eq490 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq846 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq843 X0 x X2
       have i₂ := eq668 (M.op X2 (M.op X2 X0)) x
       grind)
    | exact superpose eq668 eq843
    | exact resolve eq843 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq869 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq846 X0 X2
       have i₂ := eq474 X2 X0
       grind)
    | exact superpose eq474 eq846
    | exact resolve eq846 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq846
  have eq1167 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq143 x y
       grind)
    | exact superpose eq143 eq16
    | (have j1 := eq143 x y
       grind)
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq1479 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq563 (M.op X1 X0) X1 X1
       have i₂ := eq563 X0 X1 X1
       grind)
    | exact superpose eq563 eq563
    | exact resolve eq563 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2279 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq519 (M.op x (M.op x X0))
       have i₂ := eq869 X0 x
       grind)
    | exact superpose eq869 eq519
    | exact resolve eq519 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq4662 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1167
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1167
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq1167
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1167
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1167 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq4663 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq4662
  have eq5013 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X2 (M.op X2 (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq441 X0 X1 X2
       have i₂ := eq519 X0
       grind)
    | exact superpose eq519 eq441
    | exact resolve eq441 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq5045 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op X1 (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq5013 X0 (σ (M.op X0 X0)) x
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq5013
    | exact resolve eq5013 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5013
  have eq5188 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq5045 X0 X1
       have i₂ := eq1479 X0 X0
       grind)
    | exact superpose eq1479 eq5045
    | exact resolve eq5045 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479 eq5045
  have eq5254 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5188 X0 X1
       have i₂ := eq2279 X0 X0
       grind)
    | exact superpose eq2279 eq5188
    | exact resolve eq5188 eq2279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2279 eq5188
  have eq5399 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X1 (σ (M.op X2 (M.op X2 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5254 (M.op X2 (M.op X2 X0)) X1
       have i₂ := eq563 X0 X2 (M.op X2 (M.op X2 X0))
       grind)
    | exact superpose eq563 eq5254
    | exact resolve eq5254 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq5254
  have eq46997 : (M.op y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4663
       grind)
    | exact superpose eq4663 eq10
    | exact resolve eq10 eq4663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4663
  have eq47093 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq46997
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq46997
    | exact resolve eq46997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46997
  have eq47094 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47093
  have eq47135 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq506 y
       have i₂ := eq47094
       grind)
    | exact superpose eq47094 eq506
    | exact resolve eq506 eq47094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq47136 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq519 y
       have i₂ := eq47094
       grind)
    | exact superpose eq47094 eq519
    | exact resolve eq519 eq47094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq47204 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq490 y y X0
       have i₂ := eq47094
       grind)
    | exact superpose eq47094 eq490
    | exact resolve eq490 eq47094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq47094
  have eq47269 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq47204 x
       have i₂ := eq668 y x
       grind)
    | exact superpose eq668 eq47204
    | exact resolve eq47204 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq47204
  have eq103807 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op X0 (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq5399 y X0 x
       have i₂ := eq47135
       grind)
    | exact superpose eq47135 eq5399
    | exact resolve eq5399 eq47135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5399 eq47135
  have eq104548 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq103807 x
       have i₂ := eq537 x x
       grind)
    | exact superpose eq537 eq103807
    | exact resolve eq103807 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq103807
  have eq285534 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq104548
       have i₂ := eq47269
       grind)
    | exact superpose eq47269 eq104548
    | exact resolve eq104548 eq47269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47269 eq104548
  have eq285684 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq285534
  have eq1155262 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq47136
       grind)
    | exact superpose eq47136 eq16
    | exact resolve eq16 eq47136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47136
  have eq1155718 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1155262
       have r₂ := eq285684
       grind)
    | exact resolve eq1155262 eq285684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285684 eq1155262
  have eq1155960 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1155718
       grind)
    | exact superpose eq1155718 eq10
    | exact resolve eq10 eq1155718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155718
  have eq1156504 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1155960
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1155960
    | exact resolve eq1155960 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155960
  have eq1156505 : x = y := by grind
  clear eq1156504
  have eq1156541 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1156505
       grind)
    | exact superpose eq1156505 eq16
    | exact resolve eq16 eq1156505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156505
  have eq1156542 : False := by grind
  exact eq1156542
