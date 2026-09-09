import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_y_pxx_pyx_Equation4393 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq210 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq50 x
       have i₂ := eq14 x X0 X1
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq50 x
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq350 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq210 (M.op x X1) X1
       have i₂ := eq210 x X1
       grind)
    | (have i₁ := eq210 (M.op x y) y
       have i₂ := eq210 x X1
       grind)
    | exact superpose eq210 eq210
    | exact resolve eq210 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq65 X1 X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq785 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq780 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq790 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq785 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq785 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq785 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq785 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq802 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq790 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq790
    | (have j0 := eq790 X0 X1
       grind)
    | exact resolve eq790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq6445 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq802
  have eq6560 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6445
  have eq6561 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6560 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6560
  have eq7004 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6561 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6561
    | (have j0 := eq6561 y
       grind)
    | exact resolve eq6561 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7010 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq6561 X0
       grind)
    | exact superpose eq6561 eq50
    | exact resolve eq50 eq6561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq7013 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq210 (σ X0) (σ X0)
       have i₂ := eq6561 X0
       grind)
    | exact superpose eq6561 eq210
    | exact resolve eq210 eq6561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7063 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq7004
       grind)
    | exact superpose eq7004 eq16
    | exact resolve eq16 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq7531 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq350 eq7010
    | exact resolve eq7010 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7010
  have eq7563 : (M.op (M.op x y) y) = (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq7531
       have i₂ := eq6561 (M.op sF0 y)
       grind)
    | exact superpose eq6561 eq7531
    | exact resolve eq7531 eq6561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6561 eq7531
  have eq7579 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq350 eq7563
    | exact resolve eq7563 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7563
  have eq7587 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq7579 eq16
    | exact resolve eq16 eq7579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12249 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq12250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12249
    | exact resolve eq12249 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12249
  have eq12263 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12250
       have r₂ := eq28
       grind)
    | exact resolve eq12250 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12250
  have eq12266 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12263
    | exact resolve eq12263 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12263
  have eq12268 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12266 eq7063
    | exact resolve eq7063 eq12266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7063 eq12266
  have eq12282 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq12268
    | exact resolve eq12268 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12268
  have eq12283 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12282
  have eq12296 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7013 y
       have i₂ := eq12283
       grind)
    | exact superpose eq12283 eq7013
    | exact resolve eq7013 eq12283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7013
  have eq12299 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq210 y y
       have i₂ := eq12283
       grind)
    | exact superpose eq12283 eq210
    | exact resolve eq210 eq12283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq12283
  have eq12303 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12299
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12299
    | exact resolve eq12299 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12299
  have eq12304 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12296
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12296
    | exact resolve eq12296 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12296
  have eq12312 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12304
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12304
    | exact resolve eq12304 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12304
  have eq12314 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12312
    | exact resolve eq12312 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12312
  have eq12523 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12303 eq7579
    | exact resolve eq7579 eq12303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12531 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq12523
    | exact resolve eq12523 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12523
  have eq12533 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12531 eq215
    | exact resolve eq215 eq12531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12536 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12533
    | exact resolve eq12533 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12533
  have eq12756 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12314 eq12303
    | exact resolve eq12303 eq12314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12303 eq12314
  have eq12762 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12756
  have eq12768 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12762 eq215
    | exact resolve eq215 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq12770 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq12772 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12768
    | exact resolve eq12768 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12768
  have eq13807 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12536 eq350
    | exact resolve eq350 eq12536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13815 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12536 eq7587
    | exact resolve eq7587 eq12536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12536
  have eq14039 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12531 eq13815
    | exact resolve eq13815 eq12531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13815
  have eq14073 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq14039
  have eq14075 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq14073
    | exact resolve eq14073 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14073
  have eq14545 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12772 eq350
    | exact resolve eq350 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14553 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12772 eq7587
    | exact resolve eq7587 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7587 eq12772
  have eq14634 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12762 eq14553
    | exact resolve eq14553 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14553
  have eq14670 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq14634
  have eq14672 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14670
       have r₂ := eq12770
       grind)
    | exact resolve eq14670 eq12770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14670
  have eq14673 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq14672
    | exact resolve eq14672 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14672
  have eq14677 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq14673 eq28
    | exact resolve eq28 eq14673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14673
  have eq14697 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14677
       have r₂ := eq14075
       grind)
    | exact resolve eq14677 eq14075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14075 eq14677
  have eq15103 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12531 eq13807
    | exact resolve eq13807 eq12531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12531 eq13807
  have eq15119 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15103
  have eq15166 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12762 eq14545
    | exact resolve eq14545 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12762 eq14545
  have eq15184 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15166
  have eq15191 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15184 X0
       grind)
    | (have r₁ := eq15184 X0
       have r₂ := eq12770
       grind)
    | exact resolve eq15184 eq12770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12770 eq15184
  have eq15229 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14697 eq15119
    | exact resolve eq15119 eq14697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15119
  have eq15251 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15229
  have eq15324 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14697 eq15191
    | exact resolve eq15191 eq14697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14697 eq15191
  have eq15346 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15324
  have eq16086 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15251 y
       grind)
    | exact superpose eq15251 eq19
    | (have j1 := eq15251 y
       grind)
    | exact resolve eq19 eq15251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15251
  have eq16101 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq16086
  have eq17334 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15346 y
       grind)
    | exact superpose eq15346 eq19
    | (have j1 := eq15346 y
       grind)
    | exact resolve eq19 eq15346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15346
  have eq17349 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17334
  have eq17368 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17349 eq28
    | exact resolve eq28 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17349
  have eq17392 : x = (M.op x y) := by
    first
    | (have r₁ := eq17368
       have r₂ := eq16101
       grind)
    | exact resolve eq17368 eq16101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16101 eq17368
  have eq17393 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17392 eq21
    | exact resolve eq21 eq17392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17446 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq17392 eq350
    | exact resolve eq350 eq17392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq17460 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17392 eq7579
    | exact resolve eq7579 eq17392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7579
  have eq17464 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq17460
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17460
    | exact resolve eq17460 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17460
  have eq17478 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq17446 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17446
    | (have j0 := eq17446 X0
       grind)
    | exact resolve eq17446 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17446
  have eq17530 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17393
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17393
    | exact resolve eq17393 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17393
  have eq17532 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq17464
    | exact resolve eq17464 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17464
  have eq17540 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq17392 eq17478
    | exact resolve eq17478 eq17392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17478
  have eq17543 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq17392 eq17532
    | exact resolve eq17532 eq17392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17392 eq17532
  have eq17553 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq17530 eq27
    | exact resolve eq27 eq17530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17530
  have eq18258 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq17543 eq17553
    | exact resolve eq17553 eq17543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17553
  have eq18259 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18258
       have i₂ := eq17540 sF3
       grind)
    | exact superpose eq17540 eq18258
    | exact resolve eq18258 eq17540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17540 eq18258
  have eq18264 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq18259 eq28
    | exact resolve eq28 eq18259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18259
  have eq18294 : False := by grind
  exact eq18294

/-- `Equation4399`: `x ◇ (x ◇ y) = (x ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation4399 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4399 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4399.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19
    | exact resolve eq19 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq48
    | exact resolve eq48 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq15
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq68
    | exact resolve eq68 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq68
  have eq91 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq16
    | (have j1 := eq91 x y
       grind)
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq125 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq96
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq96
       have r₂ := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq96 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq126 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq125
  have eq238 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (σ y)
       have i₂ := eq126
       grind)
    | exact superpose eq126 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq126
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq126
       grind)
    | exact resolve eq13 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq5837 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq238 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq5838 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq5837
  have eq5878 : (k (τ (σ x)) (τ (σ y))) = (τ (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq48 (σ y) (σ x)
       have i₂ := eq5838
       grind)
    | exact superpose eq5838 eq48
    | exact resolve eq48 eq5838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5838
  have eq5886 : (k (τ (σ x)) (τ (σ y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq5878
       have i₂ := eq71 (σ x)
       grind)
    | exact superpose eq71 eq5878
    | exact resolve eq5878 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5878
  have eq5887 : (M.op x x) = (k x (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq5886
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5886
    | exact resolve eq5886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5886
  have eq5888 : (M.op x x) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq5887
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5887
    | exact resolve eq5887 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5887
  have eq5889 : (M.op x x) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq5888
       have r₂ := eq13 x y
       grind)
    | exact resolve eq5888 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5888
  have eq5897 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq5889
       grind)
    | exact superpose eq5889 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq5889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5899 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq5889
       grind)
    | exact superpose eq5889 eq15
    | exact resolve eq15 eq5889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5889
  have eq5900 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq5897
  have eq5904 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5899
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq5899
    | exact resolve eq5899 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5899
  have eq5908 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq5900
       grind)
    | exact superpose eq5900 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq5900
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq5900
       grind)
    | exact resolve eq12 eq5900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5900
  have eq5964 : (M.op y y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq5908
  have eq6013 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq5964
       grind)
    | exact superpose eq5964 eq15
    | exact resolve eq15 eq5964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5964
  have eq6018 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6013
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq6013
    | exact resolve eq6013 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6013
  have eq6020 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq6018
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq6018 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6018
  have eq6026 : (τ (M.op (σ y) (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq48 (σ y) (σ x)
       have i₂ := eq6020
       grind)
    | exact superpose eq6020 eq48
    | exact resolve eq48 eq6020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6034 : (τ (M.op (σ y) (σ y))) = (k (τ (σ x)) y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6026
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6026
    | exact resolve eq6026 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6026
  have eq6035 : (τ (M.op (σ y) (σ y))) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6034
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6034
    | exact resolve eq6034 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6034
  have eq6036 : (M.op (τ (σ y)) (τ (σ y))) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6035
       have i₂ := eq71 (σ y)
       grind)
    | exact superpose eq71 eq6035
    | exact resolve eq6035 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6035
  have eq6037 : (M.op y y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6036
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6036
    | exact resolve eq6036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6036
  have eq6041 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq6037
       grind)
    | exact superpose eq6037 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq6037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6037
  have eq6044 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq6041
  have eq6050 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6044
       grind)
    | exact superpose eq6044 eq16
    | exact resolve eq16 eq6044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6044
  have eq6133 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6050
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq6050
    | exact resolve eq6050 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050
  have eq6526 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 (σ x) (σ y)
       have i₂ := eq5904
       grind)
    | exact superpose eq5904 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq5904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5904
  have eq6529 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq6526
  have eq6648 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6529
       grind)
    | exact superpose eq6529 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq6529
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6529
       grind)
    | exact resolve eq12 eq6529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6529
  have eq6702 : (M.op y y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq6648
  have eq6757 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq6702
       grind)
    | exact superpose eq6702 eq15
    | exact resolve eq15 eq6702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6702
  have eq6762 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6757
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq6757
    | exact resolve eq6757 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6757
  have eq6764 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq6762
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq6762 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6762
  have eq6771 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14 (σ x) (σ y)
       have i₂ := eq6764
       grind)
    | exact superpose eq6764 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq6764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6772 : (τ (M.op (σ y) (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq48 (σ y) (σ x)
       have i₂ := eq6764
       grind)
    | exact superpose eq6764 eq48
    | exact resolve eq48 eq6764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq6764
  have eq6774 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq6771
  have eq6777 : (τ (M.op (σ y) (σ y))) = (k (τ (σ x)) y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6772
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6772
    | exact resolve eq6772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6772
  have eq6778 : (τ (M.op (σ y) (σ y))) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6777
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6777
    | exact resolve eq6777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6777
  have eq6779 : (M.op (τ (σ y)) (τ (σ y))) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6778
       have i₂ := eq71 (σ y)
       grind)
    | exact superpose eq71 eq6778
    | exact resolve eq6778 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq6778
  have eq6780 : (M.op y y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6779
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6779
    | exact resolve eq6779 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6779
  have eq6798 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6133
       have i₂ := eq6774
       grind)
    | exact superpose eq6774 eq6133
    | (have r₁ := eq6133
       have r₂ := eq6774
       grind)
    | exact resolve eq6133 eq6774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6861 : (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq6798
  have eq6978 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq6861
       grind)
    | exact superpose eq6861 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6861
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq6861
       grind)
    | exact resolve eq13 eq6861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8565 : (M.op x x) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j0 := eq6978 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6978
  have eq8601 : (M.op y y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6780
       have i₂ := eq8565
       grind)
    | exact superpose eq8565 eq6780
    | exact resolve eq6780 eq8565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6780 eq8565
  have eq8606 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq8601
  have eq8613 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8606
       grind)
    | exact superpose eq8606 eq16
    | exact resolve eq16 eq8606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8606
  have eq8719 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq8613
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq8613
    | exact resolve eq8613 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8613
  have eq8726 : (M.op y y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq8719
       have r₂ := eq6774
       grind)
    | exact resolve eq8719 eq6774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8719
  have eq8730 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6861
       have i₂ := eq8726
       grind)
    | exact superpose eq8726 eq6861
    | exact resolve eq6861 eq8726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6861 eq8726
  have eq8817 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq8730
  have eq8895 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8817
       grind)
    | exact superpose eq8817 eq16
    | exact resolve eq16 eq8817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8817
  have eq8999 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8895
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq8895
    | exact resolve eq8895 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895
  have eq9006 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq8999
       have r₂ := eq6774
       grind)
    | exact resolve eq8999 eq6774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6774 eq8999
  have eq9199 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6020
       have i₂ := eq9006
       grind)
    | exact superpose eq9006 eq6020
    | exact resolve eq6020 eq9006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6020
  have eq9264 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (σ y)
       have i₂ := eq9006
       grind)
    | exact superpose eq9006 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9006
       grind)
    | exact resolve eq13 eq9006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10819 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq9264 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9264
  have eq10829 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9199
       have i₂ := eq10819
       grind)
    | exact superpose eq10819 eq9199
    | exact resolve eq9199 eq10819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9199 eq10819
  have eq10835 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq10829
  have eq10840 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq10835
       have r₂ := eq6133
       grind)
    | exact resolve eq10835 eq6133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6133 eq10835
  have eq10941 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq70 y
       have i₂ := eq10840
       grind)
    | exact superpose eq10840 eq70
    | exact resolve eq70 eq10840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq10840
  have eq11092 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10941
       have i₂ := eq9006
       grind)
    | exact superpose eq9006 eq10941
    | exact resolve eq10941 eq9006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9006 eq10941
  have eq11196 : False := by grind
  exact eq11196

/-- `Equation4413`: `x ◇ (x ◇ y) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pxy_Equation4413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X3) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X2 X0) X3
       have i₂ := eq16 X2 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 x X0 X3
       have i₂ := eq16 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 X0 y x
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq182
    | (have j0 := eq182 X0 (σ y) (σ x)
       grind)
    | exact resolve eq182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op y X1) X1) := by
    intro X1
    first
    | (have i₁ := eq16 x y X1
       have i₂ := eq631 x
       grind)
    | (have i₁ := eq16 x y x
       have i₂ := eq631 x
       grind)
    | exact superpose eq631 eq16
    | (have j0 := eq16 x y X1
       grind)
    | exact resolve eq16 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X1) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq177 (M.op y X0) X0 X1
       have i₂ := eq666 X0
       grind)
    | exact superpose eq666 eq177
    | exact resolve eq177 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq898 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq909 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq940 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq898
       grind)
    | exact superpose eq898 eq41
    | exact resolve eq41 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq941 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq940
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq940
    | exact resolve eq940 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq940
  have eq943 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq941
    | exact resolve eq941 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq943 eq909
    | exact resolve eq909 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq943
  have eq960 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq953
       have r₂ := eq27
       grind)
    | exact resolve eq953 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq968 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq960 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq960
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq960
       grind)
    | exact resolve eq13 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1013 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq974 eq960
    | exact resolve eq960 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq974
  have eq1031 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1013
  have eq1066 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1031 eq153
    | exact resolve eq153 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1031
  have eq1069 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq1066
    | exact resolve eq1066 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1066
  have eq1072 : y = (M.op y y) := by
    first
    | (have j1 := eq914 y
       grind)
    | (have r₁ := eq1069
       have r₂ := eq914 y
       grind)
    | exact resolve eq1069 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1077 : (M.op x (M.op x y)) = (M.op y y) := by
    first
    | (have i₁ := eq631 y
       have i₂ := eq1072
       grind)
    | exact superpose eq1072 eq631
    | exact resolve eq631 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq1079 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1072
       grind)
    | exact superpose eq1072 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1072
       grind)
    | exact resolve eq13 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq182 X0 y y
       have i₂ := eq1072
       grind)
    | exact superpose eq1072 eq182
    | exact resolve eq182 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq1079 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq1087 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1084 X0
       have i₂ := eq1072
       grind)
    | exact superpose eq1072 eq1084
    | exact resolve eq1084 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1092 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1077
       have i₂ := eq1072
       grind)
    | exact superpose eq1072 eq1077
    | exact resolve eq1077 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1118 : y = (k y y) := by
    first
    | (have i₁ := eq1072
       have i₂ := eq1085 y
       grind)
    | exact superpose eq1085 eq1072
    | exact resolve eq1072 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1127 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k y (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 y X0 X1
       have i₂ := eq1085 (M.op y X0)
       grind)
    | exact superpose eq1085 eq182
    | exact resolve eq182 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1144 : ∀ X0 X1 : G, (k y (k y X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1127 X0 X1
       have i₂ := eq1085 X0
       grind)
    | exact superpose eq1085 eq1127
    | exact resolve eq1127 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1168 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1118
       grind)
    | exact superpose eq1118 eq41
    | exact resolve eq41 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1118
  have eq1171 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1168
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1168
    | exact resolve eq1168 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1176 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1171 eq914
    | (have j0 := eq914 (σ y)
       grind)
    | (have r₁ := eq914 (σ y)
       have r₂ := eq1171
       grind)
    | exact resolve eq914 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq1171
  have eq1177 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1176
  have eq1185 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1177 eq632
    | exact resolve eq632 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq1187 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq1177 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq1177
       grind)
    | exact resolve eq13 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1190 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1177 eq177
    | exact resolve eq177 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1193 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq1187 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1197 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) X0) := by
    intro X0
    first
    | exact superpose eq1177 eq1190
    | exact resolve eq1190 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1200 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1177 eq1185
    | exact resolve eq1185 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq1185
  have eq1204 : ∀ X0 : G, (σ y) = (M.op (k (σ y) X0) X0) := by
    intro X0
    first
    | exact superpose eq1193 eq1197
    | exact resolve eq1197 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1214 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1200 eq182
    | exact resolve eq182 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1215 : (M.op (σ x) (σ y)) = (k y (k y (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1214 x
       have i₂ := eq1144 sF4 x
       grind)
    | exact superpose eq1144 eq1214
    | exact resolve eq1214 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1221 : (M.op (σ x) (σ y)) = (k y (k y (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq1215
    | exact resolve eq1215 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1215
  have eq1251 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op y (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1 (M.op X0 y)
       have i₂ := eq1087 X0
       grind)
    | exact superpose eq1087 eq177
    | exact resolve eq177 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1253 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (M.op X1 y) X1
       have i₂ := eq1087 X1
       grind)
    | exact superpose eq1087 eq182
    | exact resolve eq182 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1264 : ∀ X1 : G, (M.op X1 y) = (k y (k y (M.op X1 y))) := by
    intro X1
    first
    | (have i₁ := eq1253 x X1
       have i₂ := eq1144 (M.op X1 y) x
       grind)
    | exact superpose eq1144 eq1253
    | exact resolve eq1253 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1266 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k y (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1251 X0 X1
       have i₂ := eq1085 (M.op X0 y)
       grind)
    | exact superpose eq1085 eq1251
    | exact resolve eq1251 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1691 : ∀ X0 X1 X2 : G, (k y (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op y X0) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X0 X1 y X2
       have i₂ := eq1085 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq1085 eq175
    | exact resolve eq175 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1773 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) X0) = (k y (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1691 X0 X1 x
       have i₂ := eq713 X0 x
       grind)
    | exact superpose eq713 eq1691
    | exact resolve eq1691 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq1691
  have eq1925 : ∀ X0 : G, (M.op (M.op x (M.op x y)) X0) = (k y (k y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq1773 X0 x
       have i₂ := eq1266 X0 x
       grind)
    | exact superpose eq1266 eq1773
    | exact resolve eq1773 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq1773
  have eq2068 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq1925 X0
       have i₂ := eq1264 X0
       grind)
    | exact superpose eq1264 eq1925
    | exact resolve eq1925 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq1925
  have eq2193 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq1092 eq2068
    | exact resolve eq2068 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq2068
  have eq2295 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2193 X0
       have i₂ := eq1085 X0
       grind)
    | exact superpose eq1085 eq2193
    | exact resolve eq2193 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq2193
  have eq2567 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2295 x
       grind)
    | exact superpose eq2295 eq18
    | (have j1 := eq2295 x
       grind)
    | exact resolve eq18 eq2295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2295
  have eq2633 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2567
       grind)
    | exact superpose eq2567 eq40
    | exact resolve eq40 eq2567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2567
  have eq2634 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2633
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2633
    | exact resolve eq2633 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2633
  have eq2636 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq2634
    | exact resolve eq2634 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2634
  have eq2765 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (k (σ y) (σ x))) := by
    first
    | exact superpose eq1193 eq181
    | exact resolve eq181 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2768 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (σ y) (k (σ y) (σ x))) := by
    first
    | exact superpose eq1193 eq2765
    | exact resolve eq2765 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765
  have eq2802 : (k (σ y) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2636 eq2768
    | exact resolve eq2768 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq2845 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2636 eq1204
    | exact resolve eq1204 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2857 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (k (σ y) X1) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1204 eq182
    | exact resolve eq182 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1204
  have eq2871 : ∀ X1 : G, (k y (k y X1)) = (M.op (k (σ y) X1) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq2857 x X1
       have i₂ := eq1144 X1 x
       grind)
    | exact superpose eq1144 eq2857
    | exact resolve eq2857 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857
  have eq2905 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq2845 eq16
    | exact resolve eq16 eq2845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq2917 : (M.op (σ y) (σ x)) = (k y (k y (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2905 x
       have i₂ := eq1144 sF1 x
       grind)
    | exact superpose eq1144 eq2905
    | exact resolve eq2905 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2905
  have eq2924 : (k (σ y) (σ x)) = (k y (k y (σ (M.op x y)))) := by
    first
    | exact superpose eq1193 eq2917
    | exact resolve eq2917 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq2917
  have eq2928 : (σ (M.op x y)) = (k y (k y (σ (M.op x y)))) := by
    first
    | exact superpose eq2636 eq2924
    | exact resolve eq2924 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2636 eq2924
  have eq2967 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq2802 eq16
    | exact resolve eq16 eq2802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802
  have eq2979 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (k y (k y (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq2871 eq2967
    | exact resolve eq2967 eq2871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871 eq2967
  have eq2987 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2928 eq2979
    | exact resolve eq2979 eq2928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928 eq2979
  have eq2993 : (σ (M.op x y)) = (k y (k y (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2987 x
       have i₂ := eq1144 sF4 x
       grind)
    | exact superpose eq1144 eq2987
    | exact resolve eq2987 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144 eq2987
  have eq3187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2993 eq1221
    | exact resolve eq1221 eq2993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq2993
  have eq3192 : False := by grind
  exact eq3192

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4417 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4417 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
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
  have eq51 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 (M.op X1 x) X3
       have i₂ := eq14 X1 x X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X0)) X3) = (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 x X3
       have i₂ := eq14 X1 x X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X2) X3 X1
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X2 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op x y) x) := by
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
  have eq57 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq82 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq119 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq213 : (M.op (M.op x y) x) = (M.op y (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq56 (M.op y x)
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | (have i₁ := eq56 x
       have i₂ := eq14 y x X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq57 x
       have i₂ := eq14 sF3 x x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op y y)) := by
    first
    | (have i₁ := eq215 (M.op y y)
       have i₂ := eq215 y
       grind)
    | exact superpose eq215 eq215
    | exact resolve eq215 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq221 eq221
    | exact resolve eq221 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : (M.op (M.op x y) x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op y (σ y))) := by
    first
    | exact superpose eq221 eq215
    | exact resolve eq215 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X3 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 (M.op X1 X2) X3
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X2 X1) X2 X3
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq53 (M.op X2 X1) X2 X3
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op y X0)) X1) = (M.op (M.op (M.op x y) x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y (M.op y X0) X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ y) X0)) X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X2 X1)
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq14 X2 X3 (M.op X2 X1)
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X3) = (M.op (M.op X2 X1) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X2 X3
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq14 (M.op X2 X1) X2 X3
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq58 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x y X0
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ x) X0 (σ y)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X3 (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op X0 X2) X3
       have i₂ := eq58 X0 X2 X1
       grind)
    | (have i₁ := eq53 X0 (M.op X0 X2) X3
       have i₂ := eq58 X0 X1 X2
       grind)
    | exact superpose eq58 eq53
    | exact resolve eq53 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq563 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq499 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq499
    | (have j1 := eq14 x y X0
       grind)
    | exact resolve eq499 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq579 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq502 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq502
    | (have j1 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq502 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X3 X2 (M.op X2 X1)
       have i₂ := eq53 X2 X1 X0
       grind)
    | (have i₁ := eq51 X3 X2 (M.op X2 X1)
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X3 (M.op (M.op X2 X1) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 (M.op (M.op X2 X1) X2) X3
       have i₂ := eq51 X2 X1 X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq732 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y X0 X1
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq850 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op y (σ x))) := by
    first
    | exact superpose eq579 eq215
    | exact resolve eq215 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 x)) X0) = (M.op (M.op X1 x) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x y X1 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52
    | (have j0 := eq52 x y X1 X0
       grind)
    | exact resolve eq52 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq931 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) X0) = (M.op (M.op X1 y) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y x X1 X0
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 (M.op (M.op X1 (M.op X1 X3)) X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X3 (M.op X1 (M.op X1 X3)) X2
       have i₂ := eq53 (M.op X1 (M.op X1 X3)) X1 X0
       grind)
    | (have i₁ := eq52 X1 X3 (M.op X1 (M.op X1 X3)) X2
       have i₂ := eq53 X0 X1 (M.op X1 (M.op X1 X3))
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1097 : ∀ X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op X2 (σ y)) X2) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq57 eq54
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq57
  have eq1200 : ∀ X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) := by
    intro X1
    first
    | exact superpose eq221 eq1097
    | (have j0 := eq1097 X1 (σ x)
       grind)
    | exact resolve eq1097 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1490 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq81 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1515 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1490 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq1490 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq1490 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq1490 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1525 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1515 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1515
    | (have j0 := eq1515 X0 X1
       grind)
    | exact resolve eq1515 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq6813 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op (M.op X1 (M.op y y)) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq360 eq438
    | exact resolve eq438 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq6818 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (M.op X1 (M.op y (σ x))) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq850 eq438
    | exact resolve eq438 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq6823 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op X1 (M.op y (σ y))) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq379 eq438
    | exact resolve eq438 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq6824 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op X1 (M.op (σ y) (σ y))) X1) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq373 eq438
    | exact resolve eq438 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq438
  have eq7008 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq447 eq6824
    | exact resolve eq6824 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq6824
  have eq7009 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq6823 X0 x
       have i₂ := eq444 sF3 x
       grind)
    | exact superpose eq444 eq6823
    | exact resolve eq6823 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6823
  have eq7011 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq6818 X0 x
       have i₂ := eq444 sF2 x
       grind)
    | exact superpose eq444 eq6818
    | exact resolve eq6818 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6818
  have eq7013 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq6813 X0 x
       have i₂ := eq444 y x
       grind)
    | exact superpose eq444 eq6813
    | exact resolve eq6813 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq6813
  have eq7018 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) := by
    intro X0
    first
    | exact superpose eq221 eq7008
    | exact resolve eq7008 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq7008
  have eq7019 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) := by
    intro X0
    first
    | (have i₁ := eq7009 X0
       have i₂ := eq215 (M.op sF0 x)
       grind)
    | exact superpose eq215 eq7009
    | exact resolve eq7009 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7009
  have eq7021 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | (have i₁ := eq7011 X0
       have i₂ := eq215 (M.op sF0 x)
       grind)
    | exact superpose eq215 eq7011
    | exact resolve eq7011 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7011
  have eq7023 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op (M.op x y) x)) X0) := by
    intro X0
    first
    | (have i₁ := eq7013 X0
       have i₂ := eq215 (M.op sF0 x)
       grind)
    | exact superpose eq215 eq7013
    | exact resolve eq7013 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq7013
  have eq7049 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq219 eq7018
    | exact resolve eq7018 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7201 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq7018 eq7019
    | exact resolve eq7019 eq7018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7019
  have eq7202 : (M.op (M.op x y) x) = (M.op (σ y) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq7201 eq219
    | exact resolve eq219 eq7201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq7209 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq7201 eq7049
    | exact resolve eq7049 eq7201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7049
  have eq7211 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7201 eq579
    | exact resolve eq579 eq7201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq7938 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq213 eq7023
    | exact resolve eq7023 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8144 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq502 eq7021
    | exact resolve eq7021 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq7021
  have eq8263 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq8144
       have i₂ := eq14 sF4 x sF2
       grind)
    | exact superpose eq14 eq8144
    | exact resolve eq8144 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8144
  have eq8563 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op (M.op (M.op X1 (M.op (M.op x y) x)) X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq213 eq475
    | exact resolve eq475 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq8807 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq7023 eq8563
    | exact resolve eq8563 eq7023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8563
  have eq8898 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq8807 x
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq8807
    | exact resolve eq8807 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq8807
  have eq9565 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7018 sF4
       have i₂ := eq533 sF4 sF2 x x
       grind)
    | (have i₁ := eq7018 x
       have i₂ := eq533 sF4 x sF2 x
       grind)
    | exact superpose eq533 eq7018
    | exact resolve eq7018 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq7018
  have eq9648 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq8263 eq9565
    | exact resolve eq9565 eq8263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8263 eq9565
  have eq9792 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7211 eq9648
    | exact resolve eq9648 eq7211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7211 eq9648
  have eq9864 : (M.op (M.op x y) x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7201 eq9792
    | exact resolve eq9792 eq7201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9792
  have eq10810 : (M.op (M.op (M.op x y) x) y) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq213 eq917
    | exact resolve eq917 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq917
  have eq10945 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq7938 eq10810
    | exact resolve eq10810 eq7938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7938 eq10810
  have eq12431 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (M.op (M.op (M.op X0 x) X0) x) := by
    intro X0
    first
    | exact superpose eq10945 eq437
    | exact resolve eq437 eq10945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq12517 : (M.op (M.op x (M.op x y)) x) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq12431 x
       have i₂ := eq563 x
       grind)
    | exact superpose eq563 eq12431
    | exact resolve eq12431 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12431
  have eq12531 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq8898 eq12517
    | exact resolve eq12517 eq8898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8898 eq12517
  have eq12555 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq12531 eq563
    | exact resolve eq563 eq12531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12621 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq10945 eq12555
    | exact resolve eq12555 eq10945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10945 eq12555
  have eq12649 : (M.op x (M.op x y)) = (M.op (σ y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq12621 eq7202
    | exact resolve eq7202 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7202
  have eq12663 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq12621 eq563
    | exact resolve eq563 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq12727 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) = (M.op (M.op x (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) x)) := by
    first
    | (have i₁ := eq1200 x
       have i₂ := eq732 (M.op sF4 sF2) x
       grind)
    | exact superpose eq732 eq1200
    | exact resolve eq1200 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq12728 : (M.op (M.op x (M.op x y)) (M.op (M.op (M.op x y) x) x)) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq7201 eq12727
    | exact resolve eq12727 eq7201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7201 eq12727
  have eq12729 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) (M.op (M.op (M.op x y) x) x)) := by
    first
    | exact superpose eq7209 eq12728
    | exact resolve eq12728 eq7209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7209 eq12728
  have eq12730 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) x)) := by
    first
    | exact superpose eq12621 eq12729
    | exact resolve eq12729 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12729
  have eq12731 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq12531 eq12730
    | exact resolve eq12730 eq12531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12531 eq12730
  have eq12732 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq12621 eq12731
    | exact resolve eq12731 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12731
  have eq12748 : ∀ X0 : G, (M.op (M.op X0 (M.op x (M.op x y))) X0) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq12732 eq53
    | exact resolve eq53 eq12732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq12806 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq12732 eq12748
    | exact resolve eq12748 eq12732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12748
  have eq15078 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X0 y)) X2) (M.op X0 y))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq476 X2 (M.op X0 y) (M.op (M.op X2 (M.op X0 y)) X2) X1
       have i₂ := eq931 (M.op (M.op X2 (M.op X0 y)) X2) X0
       grind)
    | exact superpose eq931 eq476
    | exact resolve eq476 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq15416 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X1 (M.op (M.op (M.op X0 y) (M.op (M.op x y) x)) (M.op X0 y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15078 X0 X1 x
       have i₂ := eq931 x X0
       grind)
    | exact superpose eq931 eq15078
    | exact resolve eq15078 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15078
  have eq15644 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X1 (M.op (M.op x y) x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq7023 eq15416
    | exact resolve eq15416 eq7023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15416
  have eq15775 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq7023 eq15644
    | exact resolve eq15644 eq7023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7023 eq15644
  have eq15845 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 y) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq12621 eq15775
    | exact resolve eq15775 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15775
  have eq34344 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 (M.op (M.op X0 y) (M.op (M.op x y) x))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq936 X1 X0 X2 y
       have i₂ := eq931 X0 X0
       grind)
    | exact superpose eq931 eq936
    | exact resolve eq936 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq936
  have eq34883 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 (M.op (M.op X0 y) (M.op x (M.op x y)))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq12621 eq34344
    | exact resolve eq34344 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34344
  have eq35056 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 (M.op x (M.op x y))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq15845 eq34883
    | exact resolve eq34883 eq15845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15845 eq34883
  have eq35159 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq12806 eq35056
    | exact resolve eq35056 eq12806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12806 eq35056
  have eq35419 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq35159 X0 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq35159
    | exact resolve eq35159 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35504 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 X1 x x
       have i₂ := eq35159 (M.op (M.op x X1) x) x
       grind)
    | exact superpose eq35159 eq645
    | exact resolve eq645 eq35159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq35522 : ∀ X0 X2 : G, (M.op x (M.op x y)) = (M.op X0 (M.op (M.op X2 X0) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq594 X0 x X0 X2
       have i₂ := eq35159 X0 (M.op X0 x)
       grind)
    | exact superpose eq35159 eq594
    | exact resolve eq594 eq35159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq35721 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq35522 X0 x
       have i₂ := eq35159 X0 x
       grind)
    | exact superpose eq35159 eq35522
    | exact resolve eq35522 eq35159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35522
  have eq35731 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X1) := by
    intro X1
    first
    | (have i₁ := eq35504 x X1
       have i₂ := eq35159 X1 x
       grind)
    | exact superpose eq35159 eq35504
    | exact resolve eq35504 eq35159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35504
  have eq38841 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq82 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq82
    | (have j0 := eq82 x
       grind)
    | exact resolve eq82 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq38922 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38841
  have eq38996 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38922
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq38922
    | exact resolve eq38922 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq38922
  have eq39060 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq38996
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq38996 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38996
  have eq39092 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq39060 eq50
    | exact resolve eq50 eq39060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq39060
  have eq43740 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1525 X0 (M.op X0 X0)
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq1525
    | (have j0 := eq1525 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1525 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq1525
  have eq43875 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq43740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43740
  have eq43876 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq43875 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43875
  have eq44532 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43876 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43876
    | (have j0 := eq43876 x
       grind)
    | exact resolve eq43876 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44603 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op (σ X0) x)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq732 (σ X0) (σ X0)
       have i₂ := eq43876 X0
       grind)
    | exact superpose eq43876 eq732
    | exact resolve eq732 eq43876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq44620 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq35159 (σ X0) (σ X0)
       have i₂ := eq43876 X0
       grind)
    | exact superpose eq43876 eq35159
    | exact resolve eq35159 eq43876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35159
  have eq44641 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq35731 eq44603
    | exact resolve eq44603 eq35731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44603
  have eq44955 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq44532
       grind)
    | exact superpose eq44532 eq16
    | exact resolve eq16 eq44532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44532
  have eq44983 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq39092 eq44955
    | exact resolve eq44955 eq39092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44955
  have eq46105 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq35731 eq44620
    | exact resolve eq44620 eq35731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35731 eq44620
  have eq46469 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq46105
       have i₂ := eq43876 (M.op x sF0)
       grind)
    | exact superpose eq43876 eq46105
    | exact resolve eq46105 eq43876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43876 eq46105
  have eq46560 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq12732 eq46469
    | exact resolve eq46469 eq12732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12732 eq46469
  have eq46634 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq46560 eq16
    | exact resolve eq16 eq46560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq70267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq70253
    | exact resolve eq70253 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70253
  have eq70279 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq70267
       have r₂ := eq28
       grind)
    | exact resolve eq70267 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70267
  have eq70283 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq70279
    | exact resolve eq70279 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70279
  have eq70290 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq70283 eq39092
    | exact resolve eq39092 eq70283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39092 eq70283
  have eq70435 : (τ (σ y)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70290
       have i₂ := eq44983
       grind)
    | exact superpose eq44983 eq70290
    | exact resolve eq70290 eq44983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44983 eq70290
  have eq70491 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq70435
    | exact resolve eq70435 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70435
  have eq70492 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq70491
  have eq70570 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44641 x
       have i₂ := eq70492
       grind)
    | exact superpose eq70492 eq44641
    | exact resolve eq44641 eq70492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44641
  have eq70631 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35419 x x
       have i₂ := eq70492
       grind)
    | exact superpose eq70492 eq35419
    | exact resolve eq35419 eq70492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35419 eq70492
  have eq70632 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70631
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70631
    | exact resolve eq70631 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70631
  have eq70688 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70570
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq70570
    | exact resolve eq70570 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70570
  have eq70737 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70688
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq70688
    | exact resolve eq70688 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq70688
  have eq70751 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq70737
    | exact resolve eq70737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70737
  have eq70873 : (M.op x y) = (M.op (σ y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq70632 eq12649
    | exact resolve eq12649 eq70632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12649
  have eq70917 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq70632 eq46560
    | exact resolve eq46560 eq70632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71042 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq70917
    | exact resolve eq70917 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70917
  have eq71103 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71042 eq9864
    | exact resolve eq9864 eq71042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71108 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12621 eq71103
    | exact resolve eq71103 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71103
  have eq71125 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq71108
    | exact resolve eq71108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71108
  have eq71641 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq70751 eq70632
    | exact resolve eq70632 eq70751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70632 eq70751
  have eq71707 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq71641
  have eq71840 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71707 eq9864
    | exact resolve eq9864 eq71707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9864
  have eq71844 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq71846 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12621 eq71840
    | exact resolve eq71840 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12621 eq71840
  have eq71863 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq71846
    | exact resolve eq71846 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71846
  have eq78154 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq71125 eq35721
    | exact resolve eq35721 eq71125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78169 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71125 eq46634
    | exact resolve eq46634 eq71125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71125
  have eq78436 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71042 eq78169
    | exact resolve eq78169 eq71042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78169
  have eq78471 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq78436
  have eq78474 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq78471
    | exact resolve eq78471 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78471
  have eq78690 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71863 eq12663
    | exact resolve eq12663 eq71863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12663
  have eq78717 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq71863 eq35721
    | exact resolve eq35721 eq71863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78732 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71863 eq46634
    | exact resolve eq46634 eq71863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46634 eq71863
  have eq79000 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71707 eq78732
    | exact resolve eq78732 eq71707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78732
  have eq79037 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq79000
  have eq79040 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq79037
       have r₂ := eq71844
       grind)
    | exact resolve eq79037 eq71844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79037
  have eq79041 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq79040
    | exact resolve eq79040 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq79040
  have eq79044 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq79041 eq28
    | exact resolve eq28 eq79041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79041
  have eq79127 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq79044
       have r₂ := eq78474
       grind)
    | exact resolve eq79044 eq78474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78474 eq79044
  have eq79223 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79127 eq70873
    | exact resolve eq70873 eq79127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70873
  have eq79236 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq79223
  have eq81388 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq71042 eq78154
    | exact resolve eq78154 eq71042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71042 eq78154
  have eq81615 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq81388 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81388
  have eq82748 : (σ y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71707 eq78690
    | exact resolve eq78690 eq71707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71707 eq78690
  have eq82821 : (σ y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq82748
  have eq82875 : (σ y) = (M.op (σ y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq82821
       have r₂ := eq71844
       grind)
    | exact resolve eq82821 eq71844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71844 eq82821
  have eq85591 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq79127 eq81615
    | exact resolve eq81615 eq79127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81615
  have eq85845 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq85591 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85591
  have eq86924 : y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79127 eq82875
    | exact resolve eq82875 eq79127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79127 eq82875
  have eq87001 : y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq86924
  have eq93868 : y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq85845 x
       grind)
    | exact superpose eq85845 eq19
    | (have j1 := eq85845 x
       grind)
    | exact resolve eq19 eq85845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85845
  have eq93925 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq93868
  have eq94873 : y = (M.op x y) ∨ y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87001 eq79236
    | exact resolve eq79236 eq87001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79236 eq87001
  have eq94946 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq94873
  have eq95056 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq94946 eq28
    | exact resolve eq28 eq94946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94946
  have eq95166 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq95056
       have r₂ := eq93925
       grind)
    | exact resolve eq95056 eq93925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93925 eq95056
  have eq95239 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq95166 eq78717
    | exact resolve eq78717 eq95166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78717 eq95166
  have eq95250 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq95239 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95239
  have eq96205 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq95250 x
       grind)
    | exact superpose eq95250 eq19
    | (have j1 := eq95250 x
       grind)
    | exact resolve eq19 eq95250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95250
  have eq96262 : y = (M.op x y) := by grind
  clear eq96205
  have eq96550 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq96262 eq21
    | exact resolve eq21 eq96262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96672 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq96262 eq35721
    | exact resolve eq35721 eq96262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35721
  have eq96698 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq96262 eq46560
    | exact resolve eq46560 eq96262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46560
  have eq96726 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq96698
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96698
    | exact resolve eq96698 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96698
  have eq96750 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq96672 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96672
    | (have j0 := eq96672 X0
       grind)
    | exact resolve eq96672 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq96672
  have eq96860 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq96550
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq96550
    | exact resolve eq96550 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq96550
  have eq96874 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq96726
    | exact resolve eq96726 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq96726
  have eq96890 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq96262 eq96750
    | exact resolve eq96750 eq96262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96750
  have eq96977 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq96262 eq96874
    | exact resolve eq96874 eq96262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96262 eq96874
  have eq97066 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq96860 eq27
    | exact resolve eq27 eq96860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq96860
  have eq99560 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq96977 eq97066
    | exact resolve eq97066 eq96977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97066
  have eq99561 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99560
       have i₂ := eq96890 sF2
       grind)
    | exact superpose eq96890 eq99560
    | exact resolve eq99560 eq96890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96890 eq99560
  have eq99567 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq99561 eq28
    | exact resolve eq28 eq99561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq99561
  have eq99676 : False := by grind
  exact eq99676

/-- `Equation4423`: `x ◇ (x ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pxy_pyy_pxy_Equation4423 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4423 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4423.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq204 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq204 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq204
    | (have j0 := eq204 (σ X0) (σ X1)
       grind)
    | exact resolve eq204 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq204 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq204 X0 (M.op X0 X0)
       grind)
    | exact superpose eq204 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq204 X0 X2
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq204 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq204 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq204 X0 (τ X1)
       grind)
    | exact superpose eq204 eq19
    | (have j1 := eq204 X0 (τ X1)
       grind)
    | exact resolve eq19 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1248 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq215 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1270 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1248 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq1279 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1271 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1271
    | exact resolve eq1271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1280 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1271 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq1271
    | exact resolve eq1271 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1285 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1280 X0
       have i₂ := eq1271 X0
       grind)
    | exact superpose eq1271 eq1280
    | exact resolve eq1280 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1286 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1279 X0
       have i₂ := eq1271 X0
       grind)
    | exact superpose eq1271 eq1279
    | exact resolve eq1279 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271 eq1279
  have eq1304 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (τ X0)
       have i₂ := eq1285 X0
       grind)
    | exact superpose eq1285 eq9
    | exact resolve eq9 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1432 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (σ X0)
       have i₂ := eq1286 X0
       grind)
    | exact superpose eq1286 eq9
    | exact resolve eq9 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1712 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq1286 X0
       grind)
    | exact superpose eq1286 eq208
    | (have j0 := eq208 X0 X1
       grind)
    | exact resolve eq208 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq2047 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1712 X0 X1
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq1712 X0 X1
       grind)
    | exact superpose eq1712 eq10
    | (have j1 := eq1712 X0 X1
       grind)
    | exact resolve eq10 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712
  have eq2095 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2047 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2047
    | (have j0 := eq2047 X0 X1
       grind)
    | exact resolve eq2047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq4263 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2095 x y
       grind)
    | exact superpose eq2095 eq16
    | (have j1 := eq2095 x y
       grind)
    | exact resolve eq16 eq2095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4285 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4263
       have i₂ := eq204 x y
       grind)
    | exact superpose eq204 eq4263
    | (have j1 := eq204 x y
       grind)
    | exact resolve eq4263 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq4263
  have eq4292 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq4285
  have eq4293 : y = (M.op x x) := by grind
  clear eq4292
  have eq4298 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq4293
       grind)
    | exact superpose eq4293 eq9
    | exact resolve eq9 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4319 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (τ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1304 x X1 X0
       have i₂ := eq4293
       grind)
    | exact superpose eq4293 eq1304
    | exact resolve eq1304 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq4323 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1432 x X1 X0
       have i₂ := eq4293
       grind)
    | exact superpose eq4293 eq1432
    | exact resolve eq1432 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq4388 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq4298 X0 (M.op X0 x)
       have i₂ := eq4298 X0 x
       grind)
    | exact superpose eq4298 eq4298
    | exact resolve eq4298 eq4298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4419 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4298 (σ X0) (σ X0)
       have i₂ := eq1286 X0
       grind)
    | exact superpose eq1286 eq4298
    | exact resolve eq4298 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq4441 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq4298 x x
       have i₂ := eq4293
       grind)
    | exact superpose eq4293 eq4298
    | exact resolve eq4298 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4788 : ∀ X1 : G, (M.op y X1) = (M.op (τ y) X1) := by
    intro X1
    first
    | (have i₁ := eq4319 x X1
       have i₂ := eq4298 X1 x
       grind)
    | exact superpose eq4298 eq4319
    | exact resolve eq4319 eq4298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319
  have eq4789 : (τ (M.op y y)) = (M.op y (τ y)) := by
    first
    | (have i₁ := eq4788 (τ y)
       have i₂ := eq1285 y
       grind)
    | exact superpose eq1285 eq4788
    | exact resolve eq4788 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq4791 : (M.op y (τ y)) = (M.op y (M.op y (τ y))) := by
    first
    | (have i₁ := eq4788 (M.op y (τ y))
       have i₂ := eq4388 (τ y)
       grind)
    | exact superpose eq4388 eq4788
    | exact resolve eq4788 eq4388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4788
  have eq4795 : (M.op y y) = (M.op y (τ y)) := by
    first
    | (have i₁ := eq4791
       have i₂ := eq4298 y (τ y)
       grind)
    | exact superpose eq4298 eq4791
    | exact resolve eq4791 eq4298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4791
  have eq4878 : (M.op y y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq4789
       have i₂ := eq4795
       grind)
    | exact superpose eq4795 eq4789
    | exact resolve eq4789 eq4795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4789 eq4795
  have eq4882 : (M.op y y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11 (M.op y y)
       have i₂ := eq4878
       grind)
    | exact superpose eq4878 eq11
    | exact resolve eq11 eq4878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4878
  have eq4919 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq4323 x X1
       have i₂ := eq4298 X1 x
       grind)
    | exact superpose eq4298 eq4323
    | exact resolve eq4323 eq4298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4298 eq4323
  have eq4922 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq227 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq227
    | exact resolve eq227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq5031 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4922 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4922
    | (have j0 := eq4922 X0 X1
       grind)
    | exact resolve eq4922 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4922
  have eq5062 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq4919 (σ X0)
       have i₂ := eq2095 y X0
       grind)
    | exact superpose eq2095 eq4919
    | (have j1 := eq2095 y X0
       grind)
    | exact resolve eq4919 eq2095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095 eq4919
  have eq5751 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq4419 x
       have i₂ := eq4293
       grind)
    | exact superpose eq4293 eq4419
    | exact resolve eq4419 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293 eq4419
  have eq5777 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5751
       grind)
    | exact superpose eq5751 eq16
    | exact resolve eq16 eq5751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5751
  have eq7674 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq5031 X0 y
       have i₂ := eq5062 X0
       grind)
    | exact superpose eq5062 eq5031
    | (have j0 := eq5031 X0 y
       have j1 := eq5062 X0
       grind)
    | exact resolve eq5031 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5031 eq5062
  have eq7702 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq7674 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7674
  have eq7891 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7702 x
       have i₂ := eq4441
       grind)
    | exact superpose eq4441 eq7702
    | (have j0 := eq7702 x
       grind)
    | exact resolve eq7702 eq4441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7702
  have eq7935 : x = (M.op y y) := by
    first
    | (have r₁ := eq7891
       have r₂ := eq5777
       grind)
    | exact resolve eq7891 eq5777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7891
  have eq7966 : x = (σ x) := by
    first
    | (have i₁ := eq4882
       have i₂ := eq7935
       grind)
    | exact superpose eq7935 eq4882
    | exact resolve eq4882 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4882
  have eq7972 : x = (M.op y x) := by
    first
    | (have i₁ := eq4388 y
       have i₂ := eq7935
       grind)
    | exact superpose eq7935 eq4388
    | exact resolve eq4388 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4388 eq7935
  have eq8093 : x = (M.op x y) := by
    first
    | (have i₁ := eq7972
       have i₂ := eq4441
       grind)
    | exact superpose eq4441 eq7972
    | exact resolve eq7972 eq4441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4441
  have eq8144 : (σ x) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq5777
       have i₂ := eq8093
       grind)
    | exact superpose eq8093 eq5777
    | exact resolve eq5777 eq8093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5777 eq8093
  have eq8151 : x ≠ (M.op y x) := by
    first
    | (have i₁ := eq8144
       have i₂ := eq7966
       grind)
    | exact superpose eq7966 eq8144
    | exact resolve eq8144 eq7966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7966 eq8144
  have eq8153 : False := by grind
  exact eq8153

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pxy_pxy_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq594 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq594 X0
       grind)
    | exact superpose eq594 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) ≠ (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 X1
       have i₂ := eq594 X1
       grind)
    | exact superpose eq594 eq602
    | (have j0 := eq602 X0 X1
       grind)
    | (have r₁ := eq602 X0 X0
       have r₂ := eq594 X0
       grind)
    | exact resolve eq602 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq2146 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq9
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq9 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2160 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq2146
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq2146
    | exact resolve eq2146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2168 : (M.op y y) = (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2160
       have i₂ := eq594 x
       grind)
    | exact superpose eq594 eq2160
    | exact resolve eq2160 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2171 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k x x) = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2168
       have i₂ := eq594 y
       grind)
    | exact superpose eq594 eq2168
    | exact resolve eq2168 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168
  have eq2172 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k x x) = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2171
       have i₂ := eq11 (σ y) (σ x)
       grind)
    | exact superpose eq11 eq2171
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq2171
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq2171 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2173 : (k x x) = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq2172
  have eq2174 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2173
       have i₂ := eq594 (σ x)
       grind)
    | exact superpose eq594 eq2173
    | exact resolve eq2173 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq2175 : (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2174
       have i₂ := eq594 (σ y)
       grind)
    | exact superpose eq594 eq2174
    | exact resolve eq2174 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2247 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2175
       grind)
    | exact superpose eq2175 eq10
    | exact resolve eq10 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2248 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2247
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2247
    | exact resolve eq2247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq2249 : (M.op x y) = (M.op y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq2248
  have eq2324 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq17 y x
       have i₂ := eq2249
       grind)
    | exact superpose eq2249 eq17
    | (have r₁ := eq17 x y
       have r₂ := eq2249
       grind)
    | (have r₁ := eq17 y x
       have r₂ := eq2249
       grind)
    | (have r₁ := eq17 (σ x) (σ y)
       have r₂ := eq2249
       grind)
    | exact resolve eq17 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249
  have eq2326 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq2324
  have eq2402 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq17 (σ y) (σ x)
       have i₂ := eq2326
       grind)
    | exact superpose eq2326 eq17
    | (have r₁ := eq17 (σ x) (σ y)
       have r₂ := eq2326
       grind)
    | (have r₁ := eq17 (σ y) (σ x)
       have r₂ := eq2326
       grind)
    | exact resolve eq17 eq2326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2326
  have eq2404 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq2402
  have eq2629 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k x x) = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2171
       have i₂ := eq2404
       grind)
    | exact superpose eq2404 eq2171
    | (have r₁ := eq2171
       have r₂ := eq2404
       grind)
    | exact resolve eq2171 eq2404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171 eq2404
  have eq2632 : (k x x) = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq2629
  have eq2784 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (M.op x y) = (M.op y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2632
       grind)
    | exact superpose eq2632 eq10
    | exact resolve eq10 eq2632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632
  have eq2785 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2784
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2784
    | exact resolve eq2784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq2786 : (M.op x y) = (M.op y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq2785
  have eq2862 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq17 y x
       have i₂ := eq2786
       grind)
    | exact superpose eq2786 eq17
    | (have r₁ := eq17 x y
       have r₂ := eq2786
       grind)
    | (have r₁ := eq17 y x
       have r₂ := eq2786
       grind)
    | exact resolve eq17 eq2786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786
  have eq2864 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq2862
  have eq2865 : (M.op x y) = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq2864
  have eq2872 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq2865
       grind)
    | exact superpose eq2865 eq9
    | exact resolve eq9 eq2865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2865
  have eq2878 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2872
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq2872
    | exact resolve eq2872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq2981 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2878
       have i₂ := eq11 (σ y) (σ x)
       grind)
    | exact superpose eq11 eq2878
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq2878
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq2878 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2982 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq2981
  have eq2985 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2982
       have i₂ := eq594 (σ x)
       grind)
    | exact superpose eq594 eq2982
    | exact resolve eq2982 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2982
  have eq2986 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2985
       have i₂ := eq594 (σ y)
       grind)
    | exact superpose eq594 eq2985
    | exact resolve eq2985 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq2985
  have eq2987 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq2986
  have eq3061 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq17 (σ y) (σ x)
       have i₂ := eq2987
       grind)
    | exact superpose eq2987 eq17
    | (have r₁ := eq17 (σ x) (σ y)
       have r₂ := eq2987
       grind)
    | (have r₁ := eq17 (σ y) (σ x)
       have r₂ := eq2987
       grind)
    | exact resolve eq17 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2987
  have eq3063 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3061
  have eq3065 : (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq3063
       have r₂ := eq2878
       grind)
    | exact resolve eq3063 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2878 eq3063
  have eq3071 : (k y y) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq3065
       grind)
    | exact superpose eq3065 eq18
    | exact resolve eq18 eq3065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3136 : (k x x) = (k y y) := by
    first
    | (have i₁ := eq3071
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq3071
    | exact resolve eq3071 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3071
  have eq18321 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq603 x y
       grind)
    | exact superpose eq603 eq9
    | (have j1 := eq603 x y
       grind)
    | exact resolve eq9 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18331 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq18321
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq18321
    | exact resolve eq18321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18321
  have eq18380 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq18331
       have i₂ := eq3136
       grind)
    | exact superpose eq3136 eq18331
    | (have r₁ := eq18331
       have r₂ := eq3136
       grind)
    | exact resolve eq18331 eq3136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136 eq18331
  have eq18381 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by grind
  clear eq18380
  have eq18430 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq18381
       have i₂ := eq603 (σ x) (σ y)
       grind)
    | exact superpose eq603 eq18381
    | (have j1 := eq603 (σ x) (σ y)
       grind)
    | (have r₁ := eq18381
       have r₂ := eq603 (σ x) (σ y)
       grind)
    | exact resolve eq18381 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq18381
  have eq18436 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq18430
  have eq18438 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq18436
       have i₂ := eq3065
       grind)
    | exact superpose eq3065 eq18436
    | (have r₁ := eq18436
       have r₂ := eq3065
       grind)
    | exact resolve eq18436 eq3065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065 eq18436
  have eq18439 : False := by grind
  exact eq18439

/-- `Equation4463`: `x ◇ (y ◇ x) = (z ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4463 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4463 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4463.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq207
  have eq689 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op x x) X4 X5
       have i₂ := eq16 X0 X1 x X2
       grind)
    | (have i₁ := eq16 (M.op X1 X0) X0 X2 x
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X4 X4) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 (M.op x x) X1 x x
       have i₂ := eq16 X0 X1 x (M.op X1 (M.op x x))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | (have i₁ := eq16 X0 X1 X2 (M.op X1 (M.op X2 X2))
       have i₂ := eq16 (M.op X2 X2) X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X2)) = (M.op X4 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq693 X2 X3 X4 (M.op x x)
       have i₂ := eq690 x X4 X0 X1
       grind)
    | (have i₁ := eq693 X2 X3 X4 (M.op x x)
       have i₂ := eq690 X0 X1 x X4
       grind)
    | exact superpose eq690 eq693
    | exact resolve eq693 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X2)) = (M.op X4 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq693 X2 X3 X4 (M.op x x)
       have i₂ := eq16 X0 X1 x X4
       grind)
    | (have i₁ := eq693 X0 X1 (M.op X1 X0) X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq693
    | exact resolve eq693 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq693
    | (have j0 := eq693 X0 X1 y x
       grind)
    | exact resolve eq693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq693
    | (have j0 := eq693 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : (M.op y (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq746 x x
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq746 (σ y) (σ x)
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq746
    | (have j0 := eq746 (σ y) (σ x)
       have j1 := eq747 y x
       grind)
    | exact resolve eq746 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq765 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X3 X2)) = (M.op X4 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq745 x x X2 X3 X4
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq745 (σ y) (σ x) X2 X3 X4
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq745
    | (have j0 := eq745 (σ y) (σ x) X2 X3 X4
       grind)
    | exact resolve eq745 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq766 : ∀ X0 X1 X4 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X4 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq744 X0 X1 x x X4
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq744 X0 X1 (σ y) (σ x) X4
       have i₂ := eq747 X0 X1
       grind)
    | exact superpose eq747 eq744
    | (have j0 := eq744 X0 X1 (σ y) (σ x) X4
       grind)
    | exact resolve eq744 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq778 : ∀ X4 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq765 x x X4
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq765 (σ y) (σ x) X4
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq765
    | (have j0 := eq765 (σ y) (σ x) X4
       grind)
    | exact resolve eq765 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq810 : ∀ X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X2 X3
    first
    | (have i₁ := eq690 x (M.op x (M.op x x)) X2 X3
       have i₂ := eq747 (M.op x x) x
       grind)
    | exact superpose eq747 eq690
    | exact resolve eq690 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq827 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq778 eq16
    | exact resolve eq16 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq778 eq28
    | (have j0 := eq28 X0 (M.op (σ y) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 X0 (M.op (σ y) (M.op (σ x) (σ y)))
       have r₂ := eq778 (M.op (σ y) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq28 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : ∀ X0 : G, (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq829 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq842 : ∀ X2 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X2) := by
    intro X2
    first
    | (have i₁ := eq827 x x X2
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq827 (σ y) (σ x) X2
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq827
    | (have j0 := eq827 (σ y) (σ x) X2
       grind)
    | exact resolve eq827 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq846 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq838 eq35
    | exact resolve eq35 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq859 : ∀ X0 : G, (k X0 (σ (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq846 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq846
    | exact resolve eq846 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq880 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq899 : (k (M.op x y) y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq764
       have i₂ := eq11 sF0 y
       grind)
    | exact superpose eq11 eq764
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq764 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq909 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq909 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq921 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq880 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq945 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq921 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq921 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq921 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq921 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq970 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq910 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq910
    | (have j0 := eq910 (σ X0)
       grind)
    | exact resolve eq910 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1009 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) ≠ (σ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ y) (M.op (σ x) (σ y)))) (σ (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq859 eq910
    | (have j0 := eq910 (σ (M.op (σ y) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq910 (σ (M.op (σ y) (M.op (σ x) (σ y))))
       have r₂ := eq859 (σ (M.op (σ y) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq910 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq1022 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ y) (M.op (σ x) (σ y)))) (σ (M.op (σ y) (M.op (σ x) (σ y))))) := by grind
  clear eq1009
  have eq2732 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq40
    | exact resolve eq40 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2733 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2732
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2732
    | exact resolve eq2732 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732
  have eq2735 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2733
    | exact resolve eq2733 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733
  have eq22944 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1022 eq810
    | exact resolve eq810 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22953 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ (M.op (σ y) (M.op (σ x) (σ y)))) (σ (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq1022 eq693
    | exact resolve eq693 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22966 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq1022 eq22953
    | exact resolve eq22953 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq22953
  have eq22987 : (M.op (σ y) (M.op (σ x) (σ y))) = (σ (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq22966 x x
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq22966 (σ y) (σ x)
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq22966
    | (have j0 := eq22966 (σ y) (σ x)
       grind)
    | exact resolve eq22966 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22966
  have eq23038 : (M.op (σ y) (M.op (σ x) (σ y))) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq22987 eq15
    | exact resolve eq15 eq22987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2735 eq902
    | exact resolve eq902 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25656 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq25649
       have r₂ := eq27
       grind)
    | exact resolve eq25649 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25649
  have eq25663 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25656 eq218
    | exact resolve eq218 eq25656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq25656
  have eq25719 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq25663
    | exact resolve eq25663 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25663
  have eq25732 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq25719
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq25719
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq25719
       have r₂ := eq13 y x
       grind)
    | exact resolve eq25719 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25719
  have eq25733 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq25732
       have r₂ := eq28 x (σ x)
       grind)
    | (have r₁ := eq25732
       have r₂ := eq28 x x
       grind)
    | exact resolve eq25732 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25732
  have eq25735 : x = (k x (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq25733 eq200
    | exact resolve eq200 eq25733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq25733
  have eq25790 : x = (k x x) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq25735
    | exact resolve eq25735 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25735
  have eq25796 : y = (k y x) := by
    first
    | (have j1 := eq945 x y
       grind)
    | (have r₁ := eq25790
       have r₂ := eq945 x x
       grind)
    | exact resolve eq25790 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq25790
  have eq25800 : x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq896
       have i₂ := eq25796
       grind)
    | exact superpose eq25796 eq896
    | exact resolve eq896 eq25796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq25802 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq25796
       grind)
    | exact superpose eq25796 eq40
    | exact resolve eq40 eq25796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq25796
  have eq25803 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq25802
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25802
    | exact resolve eq25802 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25802
  have eq25810 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25803 eq2735
    | exact resolve eq2735 eq25803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq25813 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25803 eq902
    | exact resolve eq902 eq25803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq25803
  have eq26187 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq25800
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq25800
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq25800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26208 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op x X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq810 y X0
       have i₂ := eq25800
       grind)
    | exact superpose eq25800 eq810
    | exact resolve eq810 eq25800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26211 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq25800
       grind)
    | exact superpose eq25800 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq25800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25800
  have eq26222 : x = (k y y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq26211
  have eq26223 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq26187
  have eq26250 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26222 eq26223
    | exact resolve eq26223 eq26222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26222 eq26223
  have eq26251 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq26250
  have eq26283 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq810 y X0
       have i₂ := eq25810
       grind)
    | exact superpose eq25810 eq810
    | exact resolve eq810 eq25810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25810
  have eq26337 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq25813
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq25813
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq25813 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26358 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25813 eq810
    | exact resolve eq810 eq25813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26360 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25813 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq25813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25813
  have eq26371 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26360
  have eq26372 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq26337
  have eq26394 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26371 eq26372
    | exact resolve eq26372 eq26371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26371 eq26372
  have eq26395 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26394
  have eq26729 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26395 eq116
    | exact resolve eq116 eq26395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26395
  have eq26744 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq26729
    | exact resolve eq26729 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26729
  have eq26810 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26744 eq747
    | exact resolve eq747 eq26744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26813 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26744 eq26810
    | exact resolve eq26810 eq26744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26744 eq26810
  have eq26970 : (σ x) = (τ (σ x)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26813 eq23038
    | exact resolve eq23038 eq26813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26813
  have eq26993 : x = (k y y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq26970
    | exact resolve eq26970 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26970
  have eq28695 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26208 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq26208 x
       grind)
    | exact superpose eq26208 eq18
    | (have j1 := eq26208 y
       grind)
    | exact resolve eq18 eq26208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28748 : x ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq26208
  have eq28804 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28695 eq838
    | exact resolve eq838 eq28695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28880 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28695 eq22987
    | exact resolve eq22987 eq28695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28881 : x = (M.op x x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28695 eq23038
    | exact resolve eq23038 eq28695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28909 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq28880
    | exact resolve eq28880 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28880
  have eq29231 : x = (k x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq28909
       grind)
    | exact superpose eq28909 eq175
    | exact resolve eq175 eq28909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29261 : (M.op x x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq747 x x
       have i₂ := eq28909
       grind)
    | exact superpose eq28909 eq747
    | exact resolve eq747 eq28909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29265 : x = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28909 eq29261
    | exact resolve eq29261 eq28909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28909 eq29261
  have eq29308 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq970 x
       have i₂ := eq29231
       grind)
    | exact superpose eq29231 eq970
    | (have j0 := eq970 x
       grind)
    | exact resolve eq970 eq29231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29231
  have eq29314 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq29308
  have eq29319 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29314
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29314
    | exact resolve eq29314 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29314
  have eq29480 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29265 eq842
    | exact resolve eq842 eq29265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29553 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29265 eq22944
    | exact resolve eq22944 eq29265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29555 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29265 eq22987
    | exact resolve eq22987 eq29265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29587 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29555
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29555
    | exact resolve eq29555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29555
  have eq29589 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29553 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29553
    | (have j0 := eq29553 X0
       grind)
    | exact resolve eq29553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29553
  have eq29656 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29587 eq29589
    | exact resolve eq29589 eq29587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29589
  have eq29698 : (M.op x y) = (τ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29587 eq29
    | exact resolve eq29 eq29587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30385 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29319 eq766
    | exact resolve eq766 eq29319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29319
  have eq30409 : ∀ X0 X1 : G, x = (M.op X0 (M.op (σ x) X1)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29265 eq30385
    | exact resolve eq30385 eq29265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29265 eq30385
  have eq30430 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29587 eq30409
    | exact resolve eq30409 eq29587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30409
  have eq30447 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29656 eq30430
    | exact resolve eq30430 eq29656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30430
  have eq30483 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq29480 y
       grind)
    | exact superpose eq29480 eq18
    | (have j1 := eq29480 y
       grind)
    | exact resolve eq18 eq29480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29480
  have eq30613 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30483 eq29
    | exact resolve eq29 eq30483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30483
  have eq31515 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29656 eq26
    | (have j1 := eq29656 (σ y)
       grind)
    | exact resolve eq26 eq29656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29656
  have eq31768 : (M.op (σ y) (σ x)) = (σ (M.op (σ y) (σ x))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31515 eq22987
    | exact resolve eq22987 eq31515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31515
  have eq31783 : (σ x) = (σ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30447 eq31768
    | exact resolve eq31768 eq30447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31768
  have eq32703 : x = (k x x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq28881
       grind)
    | exact superpose eq28881 eq175
    | exact resolve eq175 eq28881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32728 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1 x x
       have i₂ := eq28881
       grind)
    | exact superpose eq28881 eq693
    | exact resolve eq693 eq28881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq32733 : (M.op x x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq747 x x
       have i₂ := eq28881
       grind)
    | exact superpose eq28881 eq747
    | exact resolve eq747 eq28881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32737 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30613 eq32733
    | exact resolve eq32733 eq30613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32733
  have eq32741 : (M.op x x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32728 x x
       have i₂ := eq747 x x
       grind)
    | (have i₁ := eq32728 (σ y) (σ x)
       have i₂ := eq747 x x
       grind)
    | exact superpose eq747 eq32728
    | (have j0 := eq32728 (σ y) (σ x)
       grind)
    | exact resolve eq32728 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32728
  have eq32763 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30613 eq32703
    | exact resolve eq32703 eq30613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30613 eq32703
  have eq32769 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32737 eq32741
    | exact resolve eq32741 eq32737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32737 eq32741
  have eq32788 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28881 eq32769
    | exact resolve eq32769 eq28881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28881 eq32769
  have eq32804 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29698 eq32788
    | exact resolve eq32788 eq29698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32788
  have eq33123 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32804 eq11
    | exact resolve eq11 eq32804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32804
  have eq33134 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq33123
  have eq33141 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32763 eq33134
    | exact resolve eq33134 eq32763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32763 eq33134
  have eq33142 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq33141
  have eq33198 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33142 eq14
    | exact resolve eq14 eq33142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33142
  have eq33247 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq33198
    | exact resolve eq33198 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33198
  have eq33340 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33247 eq30447
    | exact resolve eq30447 eq33247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30447
  have eq33342 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33247 eq31783
    | exact resolve eq31783 eq33247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31783 eq33247
  have eq33351 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq33342
  have eq33353 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq33340 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33340
  have eq33365 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq33351
    | exact resolve eq33351 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33351
  have eq33366 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq33365
  have eq33416 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33366 eq29
    | exact resolve eq29 eq33366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35713 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28695 eq28748
    | exact resolve eq28748 eq28695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28695 eq28748
  have eq35718 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq35713
  have eq36565 : ∀ X0 : G, (M.op x x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq747 x x
       have i₂ := eq28804 X0
       grind)
    | exact superpose eq28804 eq747
    | (have j1 := eq28804 X0
       grind)
    | exact resolve eq747 eq28804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36569 : ∀ X0 : G, x = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28804 eq36565
    | (have j0 := eq36565 X0
       have j1 := eq28804 X0
       grind)
    | exact resolve eq36565 eq28804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28804 eq36565
  have eq37339 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq842 x
       have i₂ := eq36569 (M.op sF3 sF4)
       grind)
    | exact superpose eq36569 eq842
    | (have j1 := eq36569 X1
       grind)
    | exact resolve eq842 eq36569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37413 : ∀ X0 X1 : G, x = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq22944 X0
       have i₂ := eq36569 (M.op sF3 sF4)
       grind)
    | exact superpose eq36569 eq22944
    | (have j1 := eq36569 X1
       grind)
    | exact resolve eq22944 eq36569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37415 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22987
       have i₂ := eq36569 (M.op sF3 sF4)
       grind)
    | exact superpose eq36569 eq22987
    | (have j1 := eq36569 X0
       grind)
    | exact resolve eq22987 eq36569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36569
  have eq37454 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq37415 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37415
    | (have j0 := eq37415 X0
       grind)
    | exact resolve eq37415 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37415
  have eq37456 : ∀ X0 X1 : G, x = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq37413 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37413
    | (have j0 := eq37413 X0 X1
       grind)
    | exact resolve eq37413 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37413
  have eq37519 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq37454 eq37456
    | (have j0 := eq37456 X0 X1
       have j1 := eq37454 X1
       grind)
    | exact resolve eq37456 eq37454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37456
  have eq37555 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37454 eq910
    | (have j0 := eq910 (M.op x y)
       grind)
    | (have r₁ := eq910 (M.op x y)
       have r₂ := eq37454 (M.op x y)
       grind)
    | exact resolve eq910 eq37454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37454
  have eq37619 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by grind
  clear eq37555
  have eq37801 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37619 eq747
    | exact resolve eq747 eq37619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37810 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37619 eq37801
    | exact resolve eq37801 eq37619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37619 eq37801
  have eq37862 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37810 eq842
    | exact resolve eq842 eq37810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40123 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq37339 y X0
       grind)
    | exact superpose eq37339 eq18
    | (have j1 := eq37339 y X0
       grind)
    | exact resolve eq18 eq37339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37339
  have eq40276 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40123 eq910
    | (have j0 := eq910 (M.op x y)
       grind)
    | (have r₁ := eq910 (M.op x y)
       have r₂ := eq40123 (M.op x y)
       grind)
    | exact resolve eq910 eq40123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40123
  have eq40340 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq40276
  have eq41391 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40340 eq747
    | exact resolve eq747 eq40340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41400 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40340 eq41391
    | exact resolve eq41391 eq40340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40340 eq41391
  have eq42881 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq37519 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq37519 eq26
    | (have j1 := eq37519 (σ y) X0
       grind)
    | exact resolve eq26 eq37519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43078 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42881 eq910
    | (have j0 := eq910 (M.op x y)
       grind)
    | (have r₁ := eq910 (M.op x y)
       have r₂ := eq42881 (M.op x y)
       grind)
    | exact resolve eq910 eq42881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42881
  have eq43143 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq43078
  have eq43338 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43143 eq747
    | exact resolve eq747 eq43143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43347 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43143 eq43338
    | exact resolve eq43338 eq43143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43143 eq43338
  have eq43401 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq43347 eq842
    | exact resolve eq842 eq43347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55707 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26283 y
       grind)
    | exact superpose eq26283 eq18
    | (have j1 := eq26283 y
       grind)
    | exact resolve eq18 eq26283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26283
  have eq55929 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq55707 eq22987
    | exact resolve eq22987 eq55707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55707
  have eq55972 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq55929
    | exact resolve eq55929 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55929
  have eq56325 : x = (k x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq55972
       grind)
    | exact superpose eq55972 eq175
    | exact resolve eq175 eq55972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56343 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq810 x X0
       have i₂ := eq55972
       grind)
    | exact superpose eq55972 eq810
    | exact resolve eq810 eq55972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56358 : (M.op x x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq747 x x
       have i₂ := eq55972
       grind)
    | exact superpose eq55972 eq747
    | exact resolve eq747 eq55972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56364 : x = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq55972 eq56358
    | exact resolve eq56358 eq55972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55972 eq56358
  have eq56412 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq970 x
       have i₂ := eq56325
       grind)
    | exact superpose eq56325 eq970
    | (have j0 := eq970 x
       grind)
    | exact resolve eq970 eq56325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56325
  have eq56426 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq56412
  have eq56432 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq56426
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56426
    | exact resolve eq56426 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56426
  have eq56698 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq56364 eq22944
    | exact resolve eq22944 eq56364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22944
  have eq56700 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq56364 eq22987
    | exact resolve eq22987 eq56364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56757 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq56700
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56700
    | exact resolve eq56700 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56700
  have eq56759 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56698 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56698
    | (have j0 := eq56698 X0
       grind)
    | exact resolve eq56698 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56698
  have eq56828 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq56757 eq56759
    | exact resolve eq56759 eq56757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56759
  have eq57638 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq56432 eq766
    | exact resolve eq766 eq56432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq56432
  have eq57671 : ∀ X0 X1 : G, x = (M.op X0 (M.op (σ x) X1)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq56364 eq57638
    | exact resolve eq57638 eq56364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57638
  have eq57696 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq56757 eq57671
    | exact resolve eq57671 eq56757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57671
  have eq57716 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq56828 eq57696
    | exact resolve eq57696 eq56828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57696
  have eq58459 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq56828 eq26
    | (have j1 := eq56828 (σ y)
       grind)
    | exact resolve eq26 eq56828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58524 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq56828 eq778
    | exact resolve eq778 eq56828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq56828
  have eq66559 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq56343 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq56343 x
       grind)
    | exact superpose eq56343 eq18
    | (have j1 := eq56343 y
       grind)
    | exact resolve eq18 eq56343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56343
  have eq66708 : (M.op x y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq58459 eq66559
    | exact resolve eq66559 eq58459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58459 eq66559
  have eq66733 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq66708 eq57716
    | exact resolve eq57716 eq66708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57716 eq66708
  have eq66752 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) := by grind
  clear eq66733
  have eq66861 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) := by grind
  have eq69011 : (σ x) = (k (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq899 eq58524
    | exact resolve eq58524 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq58524
  have eq69040 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq33366 eq69011
    | exact resolve eq69011 eq33366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69011
  have eq69165 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq33366 eq69040
    | exact resolve eq69040 eq33366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69040
  have eq69267 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq33353 eq69165
    | (have j1 := eq33353 (M.op x y)
       grind)
    | exact resolve eq69165 eq33353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33353 eq69165
  have eq69268 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq69267
  have eq69344 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq66752 eq69268
    | exact resolve eq69268 eq66752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69268
  have eq69389 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq69344
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq69344 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69344
  have eq69979 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69389 eq970
    | (have j0 := eq970 (M.op x y)
       grind)
    | exact resolve eq970 eq69389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69389
  have eq69995 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq69979
  have eq70004 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq69995
    | exact resolve eq69995 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69995
  have eq70629 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq70004 eq747
    | exact resolve eq747 eq70004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70632 : x = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq56364 eq70629
    | exact resolve eq70629 eq56364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56364 eq70629
  have eq70662 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq56757 eq70632
    | exact resolve eq70632 eq56757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56757 eq70632
  have eq70685 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq66752 eq70662
    | exact resolve eq70662 eq66752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66752 eq70662
  have eq71439 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq70685 eq70004
    | exact resolve eq70004 eq70685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70004 eq70685
  have eq71487 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq71439
  have eq71595 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  have eq99828 : ∀ X0 X1 : G, (k X1 (M.op (σ x) X0)) = X1 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26358 eq838
    | exact resolve eq838 eq26358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq101057 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq99828
    | (have j0 := eq99828 (σ y) X0
       grind)
    | exact resolve eq99828 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99828
  have eq101313 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq101057 (M.op X1 X1)
       grind)
    | exact superpose eq101057 eq28
    | (have j0 := eq28 X0 (σ x)
       have j1 := eq101057 X1
       grind)
    | (have r₁ := eq28 X0 (σ x)
       have r₂ := eq101057 X0
       grind)
    | exact resolve eq28 eq101057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101348 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq747 X0 x
       have i₂ := eq101057 (M.op x X0)
       grind)
    | exact superpose eq101057 eq747
    | (have j1 := eq101057 X0
       grind)
    | exact resolve eq747 eq101057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101349 : ∀ X0 X1 : G, (k X1 (M.op (σ x) (σ y))) = X1 ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq101313 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101313
  have eq101353 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq101057 eq101348
    | (have j0 := eq101348 X0
       have j1 := eq101057 X0
       grind)
    | exact resolve eq101348 eq101057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101057 eq101348
  have eq101428 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq910 X0
       have i₂ := eq101349 (k X0 X0) x
       grind)
    | exact superpose eq101349 eq910
    | (have j0 := eq910 (M.op (σ x) (σ y))
       have j1 := eq101349 X0 x
       grind)
    | (have r₁ := eq910 (M.op (σ x) (σ y))
       have r₂ := eq101349 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq910 (σ x)
       have r₂ := eq101349 (σ x) x
       grind)
    | exact resolve eq910 eq101349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101349
  have eq101495 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq101428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101428
  have eq101604 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq842 x
       have i₂ := eq101353 (M.op sF3 sF4)
       grind)
    | exact superpose eq101353 eq842
    | (have j1 := eq101353 X1
       grind)
    | exact resolve eq842 eq101353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101682 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23038
       have i₂ := eq101353 (M.op sF3 sF4)
       grind)
    | exact superpose eq101353 eq23038
    | (have j1 := eq101353 X0
       grind)
    | exact resolve eq23038 eq101353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23038
  have eq101695 : ∀ X0 : G, (M.op x y) = (σ x) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37810
       have i₂ := eq101353 (M.op sF3 sF4)
       grind)
    | exact superpose eq101353 eq37810
    | (have j1 := eq101353 X0
       grind)
    | exact resolve eq37810 eq101353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101698 : ∀ X0 : G, (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41400
       have i₂ := eq101353 (M.op sF3 sF4)
       grind)
    | exact superpose eq101353 eq41400
    | (have j1 := eq101353 X0
       grind)
    | exact resolve eq41400 eq101353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41400 eq101353
  have eq101754 : ∀ X0 : G, (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq101698 eq101695
    | (have j0 := eq101695 X0
       have j1 := eq101698 X0
       grind)
    | exact resolve eq101695 eq101698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101695 eq101698
  have eq101755 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq101754 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101754
  have eq101758 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq101682
    | (have j0 := eq101682 X0
       grind)
    | exact resolve eq101682 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq101682
  have eq101987 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq101758 eq910
    | (have j0 := eq910 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq910 (M.op (σ x) (σ y))
       have r₂ := eq101758 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq910 eq101758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101758
  have eq102054 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq101987
  have eq102154 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq102054 eq689
    | exact resolve eq689 eq102054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102162 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102054 eq747
    | exact resolve eq747 eq102054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102165 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102054 eq102162
    | exact resolve eq102162 eq102054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102162
  have eq102171 : ∀ X2 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq102154 x x X2
       have i₂ := eq810 x x
       grind)
    | exact superpose eq810 eq102154
    | exact resolve eq102154 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102154
  have eq102194 : ∀ X2 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq102054 eq102171
    | exact resolve eq102171 eq102054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102054 eq102171
  have eq102202 : ∀ X2 : G, (M.op (σ x) (σ y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq102165 eq102194
    | exact resolve eq102194 eq102165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102194
  have eq102325 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102165 eq22987
    | exact resolve eq22987 eq102165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102342 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102165 eq37810
    | exact resolve eq37810 eq102165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102165
  have eq102387 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq102342
  have eq107728 : (M.op x y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102387 eq37810
    | exact resolve eq37810 eq102387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107766 : (M.op x y) ≠ (σ y) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq102387
  have eq107783 : (M.op x y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq107728
  have eq108791 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq747 X0 x
       have i₂ := eq101495 (M.op x X0)
       grind)
    | exact superpose eq101495 eq747
    | (have j1 := eq101495 X0
       grind)
    | exact resolve eq747 eq101495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108794 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq101495 eq108791
    | (have j0 := eq108791 X0
       have j1 := eq101495 X0
       grind)
    | exact resolve eq108791 eq101495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101495 eq108791
  have eq109140 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq101604 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq101604 eq26
    | (have j1 := eq101604 (σ y) X0
       grind)
    | exact resolve eq26 eq101604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101604
  have eq109315 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109140 eq910
    | (have j0 := eq910 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq910 (M.op (σ x) (σ y))
       have r₂ := eq109140 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq910 eq109140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109140
  have eq109382 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq109315
  have eq109480 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq109382 eq689
    | exact resolve eq689 eq109382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109488 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109382 eq747
    | exact resolve eq747 eq109382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109491 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109382 eq109488
    | exact resolve eq109488 eq109382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109488
  have eq109497 : ∀ X2 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq109480 x x X2
       have i₂ := eq810 x x
       grind)
    | exact superpose eq810 eq109480
    | exact resolve eq109480 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109480
  have eq109520 : ∀ X2 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq109382 eq109497
    | exact resolve eq109497 eq109382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109382 eq109497
  have eq109528 : ∀ X2 : G, (M.op (σ x) (σ y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq109491 eq109520
    | exact resolve eq109520 eq109491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109520
  have eq109649 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109491 eq22987
    | exact resolve eq22987 eq109491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109672 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109491 eq43347
    | exact resolve eq43347 eq109491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109491
  have eq109714 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq109672
  have eq112616 : (M.op x y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109714 eq43347
    | exact resolve eq43347 eq109714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112646 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  have eq112647 : (M.op x y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq109714
  have eq112653 : (M.op x y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq112616
  have eq112679 : (M.op x y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq112653
       have r₂ := eq112646
       grind)
    | exact resolve eq112653 eq112646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112646 eq112653
  have eq115078 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22987
       have i₂ := eq108794 (M.op sF3 sF4)
       grind)
    | exact superpose eq108794 eq22987
    | (have j1 := eq108794 X0
       grind)
    | exact resolve eq22987 eq108794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22987
  have eq115084 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq26358 X0
       have i₂ := eq108794 (M.op sF3 sF4)
       grind)
    | exact superpose eq108794 eq26358
    | (have j1 := eq108794 X1
       grind)
    | exact resolve eq26358 eq108794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26358 eq108794
  have eq115140 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq115084 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115084
  have eq115163 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq115140 X0 X1
       have j1 := eq28 X1 (σ x)
       grind)
    | (have r₁ := eq115140 X0 X1
       have r₂ := eq28 X0 (σ x)
       grind)
    | exact resolve eq115140 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq115140
  have eq115333 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115078 eq910
    | (have j0 := eq910 (σ x)
       grind)
    | (have r₁ := eq910 (σ x)
       have r₂ := eq115078 (σ x)
       grind)
    | exact resolve eq910 eq115078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115078
  have eq115433 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq115333
  have eq115952 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq115433 eq810
    | exact resolve eq810 eq115433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115968 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115433 eq747
    | exact resolve eq747 eq115433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115973 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109649 eq115968
    | exact resolve eq115968 eq109649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115968
  have eq115985 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq109649 eq115952
    | exact resolve eq115952 eq109649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115952
  have eq116004 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115433 eq115973
    | exact resolve eq115973 eq115433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115433 eq115973
  have eq121781 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq101755 eq910
    | (have j0 := eq910 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq910 (M.op (σ x) (σ y))
       have r₂ := eq101755 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq910 eq101755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101755
  have eq121849 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq121781
  have eq123167 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq121849 eq689
    | exact resolve eq689 eq121849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq123175 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq121849 eq747
    | exact resolve eq747 eq121849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123185 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq121849 eq123175
    | exact resolve eq123175 eq121849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123175
  have eq123191 : ∀ X2 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq123167 x x X2
       have i₂ := eq810 x x
       grind)
    | exact superpose eq810 eq123167
    | exact resolve eq123167 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq123167
  have eq123214 : ∀ X2 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq121849 eq123191
    | exact resolve eq123191 eq121849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121849 eq123191
  have eq123222 : ∀ X2 : G, (M.op (σ x) (σ y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq123185 eq123214
    | exact resolve eq123214 eq123185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123185 eq123214
  have eq123610 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq107783 eq11
    | exact resolve eq11 eq107783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107783
  have eq123623 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq123610
  have eq123638 : (M.op x y) = (k (σ y) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq123623
       have r₂ := eq107766
       grind)
    | exact resolve eq123623 eq107766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107766 eq123623
  have eq123768 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq115985 eq116004
    | exact resolve eq116004 eq115985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115985 eq116004
  have eq123794 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq123768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123768
  have eq130612 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112679 eq11
    | exact resolve eq11 eq112679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112679
  have eq130625 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq130612
  have eq130639 : (M.op x y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq130625
       have r₂ := eq112647
       grind)
    | exact resolve eq130625 eq112647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112647 eq130625
  have eq130684 : (k y y) = (τ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq123638 eq116
    | exact resolve eq116 eq123638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123638
  have eq130734 : (M.op x y) = (k y y) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29698 eq130684
    | exact resolve eq130684 eq29698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29698 eq130684
  have eq132407 : (k y y) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq130639 eq116
    | exact resolve eq116 eq130639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq130639
  have eq132457 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33416 eq132407
    | exact resolve eq132407 eq33416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33416 eq132407
  have eq132485 : x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26251
       have i₂ := eq130734
       grind)
    | exact superpose eq130734 eq26251
    | exact resolve eq26251 eq130734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130734
  have eq132515 : x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq132485
  have eq132529 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq132515
       have r₂ := eq35718
       grind)
    | exact resolve eq132515 eq35718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132515
  have eq133770 : x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26251
       have i₂ := eq132457
       grind)
    | exact superpose eq132457 eq26251
    | exact resolve eq26251 eq132457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26251 eq132457
  have eq133800 : x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq133770
  have eq133814 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq133800
       have r₂ := eq35718
       grind)
    | exact resolve eq133800 eq35718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133800
  have eq133858 : x = (k x x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq132529
       grind)
    | exact superpose eq132529 eq175
    | exact resolve eq175 eq132529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132529
  have eq133992 : x = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq133814
       grind)
    | exact superpose eq133814 eq175
    | exact resolve eq175 eq133814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq134026 : (M.op x x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq747 x x
       have i₂ := eq133814
       grind)
    | exact superpose eq133814 eq747
    | exact resolve eq747 eq133814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134032 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43347 eq134026
    | exact resolve eq134026 eq43347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43347 eq134026
  have eq134109 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq970 x
       have i₂ := eq133858
       grind)
    | exact superpose eq133858 eq970
    | (have j0 := eq970 x
       grind)
    | exact resolve eq970 eq133858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133858
  have eq134125 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq134109
  have eq134134 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq134125
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq134125
    | exact resolve eq134125 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134125
  have eq136701 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq970 x
       have i₂ := eq133992
       grind)
    | exact superpose eq133992 eq970
    | (have j0 := eq970 x
       grind)
    | exact resolve eq970 eq133992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq133992
  have eq136717 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq136701
  have eq136726 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq136717
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq136717
    | exact resolve eq136717 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136717
  have eq136952 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq133814
       have i₂ := eq134032
       grind)
    | exact superpose eq134032 eq133814
    | exact resolve eq133814 eq134032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133814 eq134032
  have eq137017 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq136952
  have eq139416 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq134134 eq747
    | exact resolve eq747 eq134134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139422 : (M.op x y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37810 eq139416
    | exact resolve eq139416 eq37810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37810 eq139416
  have eq139925 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq139422 eq134134
    | exact resolve eq134134 eq139422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134134
  have eq139926 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq139422 eq136726
    | exact resolve eq136726 eq139422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136726 eq139422
  have eq140005 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq139926
  have eq140006 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by grind
  clear eq139925
  have eq140047 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq137017 eq140005
    | exact resolve eq140005 eq137017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137017 eq140005
  have eq140048 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq140047
  have eq140070 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq140006 eq27
    | exact resolve eq27 eq140006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140006
  have eq140479 : (M.op x y) = (σ x) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq140070
       have r₂ := eq29587
       grind)
    | exact resolve eq140070 eq29587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140070
  have eq140557 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq140479 eq26
    | exact resolve eq26 eq140479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140479
  have eq140972 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37862 eq140557
    | exact resolve eq140557 eq37862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37862 eq140557
  have eq141294 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq140972 eq27
    | exact resolve eq27 eq140972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140972
  have eq141664 : y = (M.op x y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq141294
       have r₂ := eq29587
       grind)
    | exact resolve eq141294 eq29587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29587 eq141294
  have eq141736 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq24
       have i₂ := eq141664
       grind)
    | exact superpose eq141664 eq24
    | exact resolve eq24 eq141664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141758 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | (have i₁ := eq764
       have i₂ := eq141664
       grind)
    | exact superpose eq141664 eq764
    | exact resolve eq764 eq141664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq141779 : x = (k (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq26993
       have i₂ := eq141664
       grind)
    | exact superpose eq141664 eq26993
    | exact resolve eq26993 eq141664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26993 eq141664
  have eq141798 : x = (k (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq141779
  have eq141818 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq141736
    | exact resolve eq141736 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141736
  have eq142256 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq141758 eq102202
    | exact resolve eq102202 eq141758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102202 eq141758
  have eq142270 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq142256
  have eq144364 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq142270 eq11
    | exact resolve eq11 eq142270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142270
  have eq144377 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq144364
  have eq144414 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141798 eq144377
    | exact resolve eq144377 eq141798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141798 eq144377
  have eq145999 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq144414 eq27
    | exact resolve eq27 eq144414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144414
  have eq146239 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq145999
       have r₂ := eq141818
       grind)
    | exact resolve eq145999 eq141818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145999
  have eq146317 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq146239 eq27
    | exact resolve eq27 eq146239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146480 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) ∨ x = (σ x) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq146239 eq102325
    | exact resolve eq102325 eq146239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102325 eq146239
  have eq146535 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq146480
  have eq146578 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq146535
    | exact resolve eq146535 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146535
  have eq146673 : (M.op x y) ≠ (σ y) ∨ x = (σ x) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141818 eq146317
    | exact resolve eq146317 eq141818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146317
  have eq146681 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq146578
       have r₂ := eq71595
       grind)
    | exact resolve eq146578 eq71595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71595 eq146578
  have eq146767 : (M.op x y) = (σ y) ∨ x = (σ x) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141818 eq146681
    | exact resolve eq146681 eq141818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146681
  have eq146831 : x = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | (have r₁ := eq146767
       have r₂ := eq146673
       grind)
    | exact resolve eq146767 eq146673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146673 eq146767
  have eq147643 : x ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq146831 eq27
    | exact resolve eq27 eq146831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147835 : x = (σ x) ∨ x = (σ x) ∨ x = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq146831 eq109649
    | exact resolve eq109649 eq146831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109649 eq146831
  have eq147876 : x = (σ x) ∨ x = (σ x) ∨ x = (σ y) := by grind
  clear eq147835
  have eq147930 : x = (σ x) ∨ x = (σ x) ∨ x = (σ y) := by
    first
    | (have i₁ := eq147876
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq147876
    | exact resolve eq147876 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147876
  have eq147931 : x = (σ y) ∨ x = (σ x) := by grind
  clear eq147930
  have eq148039 : x ≠ (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq141818 eq147643
    | exact resolve eq147643 eq141818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141818 eq147643
  have eq148112 : x = (σ x) := by
    first
    | (have r₁ := eq148039
       have r₂ := eq147931
       grind)
    | exact resolve eq148039 eq147931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147931 eq148039
  have eq148168 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq148112
       grind)
    | exact superpose eq148112 eq18
    | exact resolve eq18 eq148112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq148169 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq148112
       grind)
    | exact superpose eq148112 eq22
    | exact resolve eq22 eq148112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq148232 : (M.op x y) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35718
       have i₂ := eq148112
       grind)
    | exact superpose eq148112 eq35718
    | exact resolve eq35718 eq148112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35718 eq148112
  have eq148909 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq148168 eq37519
    | (have j0 := eq37519 X0 X0
       grind)
    | exact resolve eq37519 eq148168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37519
  have eq148917 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq148168 eq115163
    | (have j0 := eq115163 X0 X0
       grind)
    | exact resolve eq115163 eq148168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115163
  have eq148920 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq148168 eq123794
    | exact resolve eq123794 eq148168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123794
  have eq155986 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq148909 eq910
    | (have j0 := eq910 (M.op x y)
       grind)
    | (have r₁ := eq910 (M.op x y)
       have r₂ := eq148909 (M.op x y)
       grind)
    | exact resolve eq910 eq148909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148909
  have eq156073 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq155986
  have eq157450 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq148917 eq910
    | (have j0 := eq910 (σ x)
       grind)
    | (have r₁ := eq910 (σ x)
       have r₂ := eq148917 (σ x)
       grind)
    | exact resolve eq910 eq148917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq148917
  have eq157560 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq157450
  have eq158290 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq156073 eq747
    | exact resolve eq747 eq156073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158317 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq156073 eq158290
    | exact resolve eq158290 eq156073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156073 eq158290
  have eq158821 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq157560 eq747
    | exact resolve eq747 eq157560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158832 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq157560 eq158821
    | exact resolve eq158821 eq157560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157560 eq158821
  have eq159390 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq158317 eq123222
    | exact resolve eq123222 eq158317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123222
  have eq159408 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq159390
  have eq159468 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq140048 eq159408
    | exact resolve eq159408 eq140048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159408
  have eq161508 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq158832 eq842
    | exact resolve eq842 eq158832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq161635 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq158832 eq109528
    | exact resolve eq109528 eq158832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109528 eq158832
  have eq161655 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq161635
  have eq161983 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq161655 eq27
    | exact resolve eq27 eq161655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162130 : (M.op x y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq161655
  have eq162358 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq71487 eq161983
    | (have r₁ := eq161983
       have r₂ := eq71487
       grind)
    | exact resolve eq161983 eq71487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161983
  have eq162363 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq162358
  have eq162374 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq162363 eq27
    | exact resolve eq27 eq162363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162589 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  have eq162694 : (σ x) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq71487 eq162374
    | exact resolve eq162374 eq71487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71487 eq162374
  have eq166384 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq161508 eq148168
    | exact resolve eq148168 eq161508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148168 eq161508
  have eq166615 : (σ x) = (σ y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq162363 eq166384
    | exact resolve eq166384 eq162363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162363
  have eq166765 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq166384
  have eq166772 : (σ x) = (σ y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq166615
  have eq166867 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq166772
       have r₂ := eq162694
       grind)
    | exact resolve eq166772 eq162694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162694 eq166772
  have eq166932 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq166867
       have r₂ := eq162589
       grind)
    | exact resolve eq166867 eq162589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162589 eq166867
  have eq167268 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq166932 eq148920
    | exact resolve eq148920 eq166932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148920 eq166932
  have eq167305 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq167268
       have r₂ := eq66861
       grind)
    | exact resolve eq167268 eq66861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66861 eq167268
  have eq167415 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq167305
    | exact resolve eq167305 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167305
  have eq167416 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq167415
  have eq167903 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq167416 eq148169
    | exact resolve eq148169 eq167416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148169 eq167416
  have eq168011 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq167903
    | exact resolve eq167903 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq167903
  have eq168012 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq168011
  have eq168160 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq168012 eq29
    | exact resolve eq29 eq168012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq168368 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq168160 eq14
    | exact resolve eq14 eq168160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168160
  have eq186255 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq159468 eq26
    | exact resolve eq26 eq159468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159468
  have eq186801 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq140048 eq186255
    | exact resolve eq186255 eq140048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140048 eq186255
  have eq186943 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq186801
       have r₂ := eq148232
       grind)
    | exact resolve eq186801 eq148232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148232 eq186801
  have eq187345 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq186943 eq747
    | exact resolve eq747 eq186943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq187354 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq186943 eq187345
    | exact resolve eq187345 eq186943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186943 eq187345
  have eq187996 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq187354 eq158317
    | exact resolve eq158317 eq187354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158317 eq187354
  have eq188022 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by grind
  clear eq187996
  have eq188419 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq188022 eq27
    | exact resolve eq27 eq188022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188846 : (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq188419
       have r₂ := eq33366
       grind)
    | exact resolve eq188419 eq33366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188419
  have eq188938 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq188846 eq26
    | exact resolve eq26 eq188846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq188846
  have eq189763 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq188938 eq43401
    | exact resolve eq43401 eq188938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43401 eq188938
  have eq189808 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq189763
  have eq189844 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq188022 eq189808
    | exact resolve eq189808 eq188022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188022 eq189808
  have eq189845 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq189844
  have eq189890 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq189845 eq27
    | exact resolve eq27 eq189845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189845
  have eq190259 : y = (M.op x y) := by
    first
    | (have r₁ := eq189890
       have r₂ := eq33366
       grind)
    | exact resolve eq189890 eq33366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33366 eq189890
  have eq190329 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq190259
       grind)
    | exact superpose eq190259 eq24
    | exact resolve eq24 eq190259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq190259
  have eq190429 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq168368 eq190329
    | exact resolve eq190329 eq168368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168368 eq190329
  have eq190760 : (M.op x y) ≠ (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq190429 eq162130
    | (have r₁ := eq162130
       have r₂ := eq190429
       grind)
    | exact resolve eq162130 eq190429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162130
  have eq190762 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq190429 eq166765
    | (have r₁ := eq166765
       have r₂ := eq190429
       grind)
    | exact resolve eq166765 eq190429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166765 eq190429
  have eq190777 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq190762
  have eq190778 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq190760
  have eq190800 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq190777 eq190778
    | exact resolve eq190778 eq190777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190777 eq190778
  have eq190801 : (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq190800
  have eq191240 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq190801 eq27
    | exact resolve eq27 eq190801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq190801
  have eq191569 : False := by grind
  exact eq191569

/-- `Equation4480`: `x ◇ (y ◇ y) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation4480 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq41
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq79 : (M.op x y) ≠ (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq12
    | (have j0 := eq12 (τ (σ x)) (τ (σ y))
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq82 sF4
       grind)
    | exact superpose eq82 eq81
    | exact resolve eq81 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq85 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq79
       have i₂ := eq82 (τ sF4)
       grind)
    | exact superpose eq82 eq79
    | exact resolve eq79 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq86 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq82 sF5
       grind)
    | exact superpose eq82 eq83
    | exact resolve eq83 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq88 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq85
       have i₂ := eq82 (τ sF5)
       grind)
    | exact superpose eq82 eq85
    | exact resolve eq85 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq123 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq146 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq153 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq154 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq151
    | (have j0 := eq151 X0 X1
       grind)
    | (have r₁ := eq151 X0 X0
       have r₂ := eq82 X0
       grind)
    | exact resolve eq151 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq155 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq150
    | (have j0 := eq150 X0 X1
       grind)
    | exact resolve eq150 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq159 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq152
    | (have j0 := eq152 X0 X1
       grind)
    | exact resolve eq152 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq163 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq153
    | (have j0 := eq153 X0 X1
       grind)
    | exact resolve eq153 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq166 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq154
    | (have j0 := eq154 X0 X1
       grind)
    | exact resolve eq154 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq167 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq155
    | (have j0 := eq155 X0 X1
       grind)
    | (have r₁ := eq155 X0 X0
       have r₂ := eq82 X0
       grind)
    | exact resolve eq155 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq171 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq159 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq159
    | (have j0 := eq159 X0 X1
       grind)
    | exact resolve eq159 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq176 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq167
    | (have j0 := eq167 X0 X1
       grind)
    | exact resolve eq167 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq180 : ∀ X0 X1 : G, (k X1 X1) = (k X1 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq171
    | (have j0 := eq171 X0 X1
       grind)
    | exact resolve eq171 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq185 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ (k X1 X1) = (k X1 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq180
    | (have j0 := eq180 X0 X1
       grind)
    | exact resolve eq180 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq188 : ∀ X0 X1 : G, (k X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       have j1 := eq176 X1 X0
       grind)
    | (have r₁ := eq185 X1 X1
       have r₂ := eq176 X1 X1
       grind)
    | (have r₁ := eq185 X0 X0
       have r₂ := eq176 X0 X0
       grind)
    | (have r₁ := eq185 X0 X1
       have r₂ := eq176 X0 X1
       grind)
    | exact resolve eq185 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq185
  have eq240 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq240
    | (have j0 := eq240 X0 X1
       grind)
    | (have r₁ := eq240 X0 X0
       have r₂ := eq82 X0
       grind)
    | exact resolve eq240 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq246 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X1 X1) ∨ (k X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq243
    | (have j0 := eq243 X0 X1
       grind)
    | (have r₁ := eq243 X0 X0
       have r₂ := eq82 X0
       grind)
    | exact resolve eq243 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq243
  have eq611 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq163
    | exact resolve eq163 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq163
    | (have j0 := eq163 (σ x) (σ y)
       grind)
    | exact resolve eq163 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq746 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq611 eq15
    | exact resolve eq15 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq746
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq746
    | exact resolve eq746 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq748 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq747
    | exact resolve eq747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq757 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq748 eq15
    | exact resolve eq15 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq757
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq757
    | exact resolve eq757 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq759 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq758
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq758
    | exact resolve eq758 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq760 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq759
    | exact resolve eq759 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq766 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq760 eq15
    | exact resolve eq15 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq770 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq766
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq766
    | exact resolve eq766 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq772 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq770
    | exact resolve eq770 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq787 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  have eq856 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X0)) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X1 X0
       have i₂ := eq188 X1 X0
       grind)
    | (have i₁ := eq123 X1 X1
       have i₂ := eq188 X0 X1
       grind)
    | exact superpose eq188 eq123
    | (have j1 := eq188 X1 X0
       grind)
    | exact resolve eq123 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k X0 X0)) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq188 X1 X0
       grind)
    | (have i₁ := eq15 X1 X1
       have i₂ := eq188 X0 X1
       grind)
    | exact superpose eq188 eq15
    | (have j1 := eq188 X1 X0
       grind)
    | exact resolve eq15 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 X0)) ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq188 (σ X1) X0
       grind)
    | (have i₁ := eq47 (σ X1) X1
       have i₂ := eq188 X0 (σ X1)
       grind)
    | exact superpose eq188 eq47
    | (have j1 := eq188 (σ X1) X0
       grind)
    | exact resolve eq47 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq188
  have eq895 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq858 X0 X1
       have i₂ := eq123 X0 X0
       grind)
    | exact superpose eq123 eq858
    | (have j0 := eq858 X0 X1
       grind)
    | exact resolve eq858 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq896 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq857 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq857
    | (have j0 := eq857 X0 X1
       grind)
    | exact resolve eq857 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq897 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (k (τ X0) (τ X0)) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq856 X0 X1
       have i₂ := eq123 X0 X0
       grind)
    | exact superpose eq123 eq856
    | (have j0 := eq856 X0 X1
       grind)
    | exact resolve eq856 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq2330 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq615 eq33
    | exact resolve eq33 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq2335 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq772 eq2330
    | (have r₁ := eq2330
       have r₂ := eq772
       grind)
    | exact resolve eq2330 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq2336 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq2335
  have eq2339 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2336 eq86
    | (have r₁ := eq86
       have r₂ := eq2336
       grind)
    | exact resolve eq86 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336
  have eq2344 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq2339
       have r₂ := eq86
       grind)
    | exact resolve eq2339 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339
  have eq2346 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq2344
       have r₂ := eq787
       grind)
    | exact resolve eq2344 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq2344
  have eq2630 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq246
    | (have j0 := eq246 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq246 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2889 : ∀ X0 X1 : G, (k (τ X0) (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (k X0 X0) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq896 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq896
    | (have j0 := eq896 (τ X0) X1
       grind)
    | exact resolve eq896 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq9905 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq611 eq2630
    | (have r₁ := eq2630
       have r₂ := eq611
       grind)
    | exact resolve eq2630 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9909 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by grind
  clear eq9905
  have eq9910 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by grind
  clear eq9909
  have eq10894 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq748
       have i₂ := eq897 sF4 sF5
       grind)
    | exact superpose eq897 eq748
    | (have j1 := eq897 (σ x) (σ y)
       grind)
    | exact resolve eq748 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748 eq897
  have eq10995 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq10894
  have eq11012 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq10995
    | exact resolve eq10995 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10995
  have eq11022 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq11012
    | exact resolve eq11012 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11012
  have eq11028 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq11022
       have r₂ := eq2330
       grind)
    | exact resolve eq11022 eq2330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330 eq11022
  have eq11120 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq11028 eq88
    | (have r₁ := eq88
       have r₂ := eq11028
       grind)
    | exact resolve eq88 eq11028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11028
  have eq11176 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq11120
  have eq11715 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ x)) (τ (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq11176 eq15
    | exact resolve eq15 eq11176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11176
  have eq11748 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11715
       have i₂ := eq15 (τ sF4) (τ sF5)
       grind)
    | exact superpose eq15 eq11715
    | exact resolve eq11715 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11715
  have eq11750 : (k (σ y) (σ y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11748
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq11748
    | exact resolve eq11748 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11748
  have eq11751 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11750
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq11750
    | exact resolve eq11750 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11750
  have eq11752 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq11751
       have r₂ := eq86
       grind)
    | exact resolve eq11751 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq11751
  have eq11794 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq11752 eq123
    | exact resolve eq123 eq11752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11752
  have eq11825 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11794
       have i₂ := eq123 sF5 sF4
       grind)
    | exact superpose eq123 eq11794
    | exact resolve eq11794 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11794
  have eq12134 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq11825 eq611
    | exact resolve eq611 eq11825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq12140 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq11825 eq2630
    | exact resolve eq2630 eq11825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630 eq11825
  have eq12199 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq12134
  have eq12212 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq12140
       have r₂ := eq9910
       grind)
    | exact resolve eq12140 eq9910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9910 eq12140
  have eq18518 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq12212 eq12199
    | exact resolve eq12199 eq12212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12199 eq12212
  have eq18541 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq18518
  have eq18711 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq18541 eq15
    | exact resolve eq15 eq18541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18541
  have eq18745 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq18711
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq18711
    | exact resolve eq18711 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18711
  have eq18746 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq18745
    | exact resolve eq18745 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18745
  have eq18749 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq18746 eq33
    | exact resolve eq33 eq18746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18746
  have eq70482 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ x) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq2889
    | (have j0 := eq2889 (σ x) (τ (σ y))
       grind)
    | exact resolve eq2889 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2889
  have eq70616 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq70482
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq70482
    | exact resolve eq70482 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70482
  have eq70778 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq70616 eq15
    | exact resolve eq15 eq70616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70616
  have eq70799 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq70778
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq70778
    | exact resolve eq70778 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70778
  have eq70802 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq70799
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq70799
    | exact resolve eq70799 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70799
  have eq70805 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq70802
    | exact resolve eq70802 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70802
  have eq70921 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq70805 eq15
    | exact resolve eq15 eq70805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70805
  have eq70956 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq70921
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq70921
    | exact resolve eq70921 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70921
  have eq70957 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq70956
    | exact resolve eq70956 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70956
  have eq70958 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq70957
       have r₂ := eq18749
       grind)
    | exact resolve eq70957 eq18749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18749 eq70957
  have eq70961 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq70958 eq2346
    | (have r₁ := eq2346
       have r₂ := eq70958
       grind)
    | exact resolve eq2346 eq70958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346 eq70958
  have eq71002 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq70961
  have eq71003 : (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq71002
  have eq71032 : (M.op x y) = (τ (k (σ x) (σ x))) := by
    first
    | exact superpose eq71003 eq36
    | exact resolve eq36 eq71003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq71054 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq71032
       have i₂ := eq123 sF4 sF4
       grind)
    | exact superpose eq123 eq71032
    | exact resolve eq71032 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq71032
  have eq71070 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq71054 eq88
    | (have r₁ := eq88
       have r₂ := eq71054
       grind)
    | exact resolve eq88 eq71054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq71073 : ∀ X0 : G, (k (σ x) (σ X0)) = (M.op (σ x) (σ X0)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (M.op x y) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq71054 eq895
    | (have j0 := eq895 (σ x) X0
       grind)
    | exact resolve eq895 eq71054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq71054
  have eq71181 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) := by grind
  clear eq71070
  have eq71976 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ x)) (τ (σ y)))) := by
    first
    | exact superpose eq71181 eq15
    | exact resolve eq15 eq71181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71181
  have eq72010 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) := by
    first
    | (have i₁ := eq71976
       have i₂ := eq15 (τ sF4) (τ sF5)
       grind)
    | exact superpose eq15 eq71976
    | exact resolve eq71976 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71976
  have eq72014 : (k (σ y) (σ y)) = (k (σ (τ (σ x))) (σ y)) := by
    first
    | (have i₁ := eq72010
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq72010
    | exact resolve eq72010 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72010
  have eq72017 : (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq72014
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq72014
    | exact resolve eq72014 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72014
  have eq72122 : ∀ X0 : G, (k (σ x) (σ y)) ≠ (k X0 (σ y)) ∨ (k X0 X0) = (M.op X0 (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq72017 eq166
    | (have j0 := eq166 X0 (σ y)
       grind)
    | (have r₁ := eq166 (σ x) (σ y)
       have r₂ := eq72017
       grind)
    | exact resolve eq166 eq72017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq79128 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j0 := eq72122 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72122
  have eq79147 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq79128
    | exact resolve eq79128 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79128
  have eq79158 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq79147
    | exact resolve eq79147 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79147
  have eq79540 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq79158
  have eq86345 : ∀ X0 : G, (k (σ x) (σ X0)) ≠ (k (σ X0) (σ X0)) ∨ (k (σ x) (σ X0)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ X0)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (M.op x y) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq71073 eq246
    | (have j0 := eq246 (σ X0) (σ x)
       have j1 := eq71073 X0
       grind)
    | (have r₁ := eq246 (σ x) (σ x)
       have r₂ := eq71073 x
       grind)
    | exact resolve eq246 eq71073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq86351 : ∀ X0 : G, (k (σ x) (σ X0)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (M.op x y) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | (have j0 := eq71073 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71073
  have eq86352 : ∀ X0 : G, (k (σ x) (σ X0)) ≠ (k (σ X0) (σ X0)) ∨ (k (σ x) (σ X0)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (M.op x y) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | (have j0 := eq86345 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86345
  have eq86355 : ∀ X0 : G, (k (σ x) (σ X0)) ≠ (k (σ X0) (σ X0)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (M.op x y) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | (have j0 := eq86352 X0
       have j1 := eq86351 X0
       grind)
    | (have r₁ := eq86352 X0
       have r₂ := eq86351 X0
       grind)
    | (have r₁ := eq86352 x
       have r₂ := eq86351 x
       grind)
    | exact resolve eq86352 eq86351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86351 eq86352
  have eq96510 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq86355 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq86355
    | (have j0 := eq86355 y
       grind)
    | exact resolve eq86355 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq86355
  have eq96544 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) y) := by
    first
    | (have r₁ := eq96510
       have r₂ := eq72017
       grind)
    | exact resolve eq96510 eq72017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72017 eq96510
  have eq96546 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) y) := by
    first
    | exact superpose eq32 eq96544
    | exact resolve eq96544 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq96544
  have eq96547 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq96546
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq96546
    | exact resolve eq96546 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq96546
  have eq96562 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq96547 eq15
    | exact resolve eq15 eq96547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96547
  have eq96585 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq96562
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq96562
    | exact resolve eq96562 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96562
  have eq96587 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq96585
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq96585
    | exact resolve eq96585 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq96585
  have eq96588 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq96587
    | exact resolve eq96587 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq96587
  have eq96589 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq71003 eq96588
    | exact resolve eq96588 eq71003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96588
  have eq96590 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq96589
       have r₂ := eq79540
       grind)
    | exact resolve eq96589 eq79540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79540 eq96589
  have eq96597 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq96590 eq33
    | exact resolve eq33 eq96590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq96590
  have eq96608 : False := by grind
  exact eq96608
