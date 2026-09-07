import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1037`: `x = x ◇ ((y ◇ (x ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if X = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_y_y_pxy_Equation1037 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1037 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1037.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq9 X0 X1 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) x)
       have i₂ := eq9 (M.op X0 (M.op X1 X1)) x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (M.op X0 X0)
       have i₂ := eq29 (M.op X0 X0) X0
       grind)
    | exact superpose eq29 eq29
    | exact resolve eq29 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq29 (M.op X0 X0) X0
       grind)
    | exact superpose eq29 eq9
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 (M.op X0 X0)) X0
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq12
    | (have j0 := eq12 (M.op X1 (M.op X0 X0)) X0
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X1 X1)) X1
       have r₂ := eq29 X0 X1
       grind)
    | exact resolve eq12 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq104 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X1 X1) X1 x
       have i₂ := eq29 (M.op X1 X1) X1
       grind)
    | exact superpose eq29 eq28
    | exact resolve eq28 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq164 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq39 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq164 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq169 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq166 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq166
    | (have j0 := eq166 X0 X1
       grind)
    | exact resolve eq166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq185 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq104 X0 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq104
    | exact resolve eq104 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq104
  have eq197 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq26
  have eq221 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq29
    | exact resolve eq29 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq254 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq221 X0
       grind)
    | exact superpose eq221 eq29
    | exact resolve eq29 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq257 : ∀ X0 X1 : G, (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq221 X0
       grind)
    | exact superpose eq221 eq37
    | exact resolve eq37 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq284 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) (σ X1)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq34
    | (have j1 := eq39 X0 X1
       grind)
    | exact resolve eq34 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq39
  have eq305 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq221 (σ X0)
       grind)
    | exact superpose eq221 eq284
    | (have j0 := eq284 X0 X1
       grind)
    | exact resolve eq284 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq532 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq257 (M.op X1 X0) X0
       have i₂ := eq254 X0 X1
       grind)
    | exact superpose eq254 eq257
    | exact resolve eq257 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (M.op X1 (τ X0))
       have i₂ := eq257 (τ X0) X1
       grind)
    | exact superpose eq257 eq19
    | exact resolve eq19 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq545 : ∀ X0 X1 : G, (k (σ (M.op X1 (τ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq544
    | exact resolve eq544 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq1305 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40
    | exact resolve eq40 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1346 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1305 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1305
    | (have j0 := eq1305 X0 X1
       grind)
    | exact resolve eq1305 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1732 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq169 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq169
    | exact resolve eq169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1739 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 y x
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 y x
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq1777 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1732 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1732
    | (have j0 := eq1732 X0 X1
       grind)
    | exact resolve eq1732 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq1782 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1777 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1777
    | (have j0 := eq1777 X0 X1
       grind)
    | exact resolve eq1777 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1777
  have eq6847 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1782 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1782
    | exact resolve eq1782 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq13855 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1739
       have i₂ := eq1346 x y
       grind)
    | exact superpose eq1346 eq1739
    | (have j1 := eq1346 x y
       grind)
    | (have r₁ := eq1739
       have r₂ := eq1346 x y
       grind)
    | (have r₁ := eq1739
       have r₂ := eq1346 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1739
       have r₂ := eq1346 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1739 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346 eq1739
  have eq13856 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq13855
  have eq14667 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq305 (τ X0) (τ X1)
       have i₂ := eq197 X1 X0
       grind)
    | exact superpose eq197 eq305
    | (have j0 := eq305 (τ X0) (τ X1)
       grind)
    | exact resolve eq305 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq305
  have eq14794 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14667 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq14667
    | (have j0 := eq14667 X0 X1
       grind)
    | exact resolve eq14667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14667
  have eq14834 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14794 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14794
    | (have j0 := eq14794 X0 X1
       grind)
    | exact resolve eq14794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14794
  have eq14863 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14834 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14834
    | (have j0 := eq14834 X0 X1
       grind)
    | exact resolve eq14834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14834
  have eq14884 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14863 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14863
    | (have j0 := eq14863 X0 X1
       grind)
    | exact resolve eq14863 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14863
  have eq14893 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14884 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14884
    | (have j0 := eq14884 X0 X1
       grind)
    | exact resolve eq14884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14884
  have eq14898 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14893 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14893
    | (have j0 := eq14893 X0 X1
       grind)
    | exact resolve eq14893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14893
  have eq18731 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6847 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6847
  have eq19799 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq254 (k X0 X1) X0
       have i₂ := eq14898 X0 X1
       grind)
    | exact superpose eq14898 eq254
    | (have j1 := eq14898 X0 X1
       grind)
    | exact resolve eq254 eq14898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14898
  have eq46029 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (σ (M.op X1 (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19799 (σ (M.op X1 (τ X0))) X0
       have i₂ := eq545 X0 X1
       grind)
    | exact superpose eq545 eq19799
    | (have j0 := eq19799 (σ (M.op X1 (τ X0))) X0
       grind)
    | exact resolve eq19799 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq46273 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (σ (M.op X1 (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46029 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46029
  have eq49487 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) ∨ (σ X0) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46273 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46273
    | exact resolve eq46273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46273
  have eq154064 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq13856
       grind)
    | exact superpose eq13856 eq10
    | exact resolve eq10 eq13856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13856
  have eq154119 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq154064
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq154064
    | exact resolve eq154064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154064
  have eq154138 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq532 x y
       have i₂ := eq154119
       grind)
    | exact superpose eq154119 eq532
    | exact resolve eq532 eq154119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq154119
  have eq154268 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq18731 x y
       grind)
    | (have r₁ := eq154138
       have r₂ := eq18731 x y
       grind)
    | exact resolve eq154138 eq18731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18731 eq154138
  have eq154462 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19799 x y
       have i₂ := eq154268
       grind)
    | exact superpose eq154268 eq19799
    | (have j0 := eq19799 x y
       grind)
    | exact resolve eq19799 eq154268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19799 eq154268
  have eq154495 : y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq154462
  have eq154718 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq254 x y
       have i₂ := eq154495
       grind)
    | exact superpose eq154495 eq254
    | exact resolve eq254 eq154495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq154843 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49487 x y
       have i₂ := eq154495
       grind)
    | exact superpose eq154495 eq49487
    | exact resolve eq49487 eq154495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49487 eq154495
  have eq154853 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq154843
  have eq157269 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq154853
       grind)
    | exact superpose eq154853 eq16
    | exact resolve eq16 eq154853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154853
  have eq157691 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq157269
       have i₂ := eq154718
       grind)
    | exact superpose eq154718 eq157269
    | exact resolve eq157269 eq154718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154718 eq157269
  have eq157694 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq157691
  have eq157695 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq157694
  have eq157728 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq157695
       grind)
    | exact superpose eq157695 eq10
    | exact resolve eq10 eq157695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157695
  have eq157867 : x = y ∨ x = y := by
    first
    | (have i₁ := eq157728
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq157728
    | exact resolve eq157728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157728
  have eq157868 : x = y := by grind
  clear eq157867
  have eq157927 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq157868
       grind)
    | exact superpose eq157868 eq16
    | exact resolve eq16 eq157868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157868
  have eq157928 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq157927
       have i₂ := eq221 x
       grind)
    | exact superpose eq221 eq157927
    | exact resolve eq157927 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157927
  have eq157929 : False := by grind
  exact eq157929

/-- `Equation104`: `x = x ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation104 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law104 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law104.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k (M.op (M.op X1 X0) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) X0) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X1 X0) X0) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X0) X0) X0
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k (M.op (M.op X1 X0) X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq19 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq10
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq10
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq36 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq26
  have eq97 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq16
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq548 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) X1)) ≠ (σ (M.op (M.op X0 X1) X1)) ∨ (σ (M.op (M.op X0 X1) X1)) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) ∨ (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X1 (M.op (M.op X0 X1) X1)
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq104
    | (have j0 := eq104 X1 (M.op (M.op X0 X1) X1)
       grind)
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq104 (τ X1) (τ X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq104
    | (have j0 := eq104 (τ X1) (τ X0)
       grind)
    | exact resolve eq104 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq559 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) X1)) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) ∨ (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq548 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq565 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq553
    | (have j0 := eq553 X0 X1
       grind)
    | exact resolve eq553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq569 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq565
    | (have j0 := eq565 X0 X1
       grind)
    | exact resolve eq565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq572 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq569 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq569
    | (have j0 := eq569 X0 X1
       grind)
    | exact resolve eq569 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq574 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq572
    | (have j0 := eq572 X0 X1
       grind)
    | exact resolve eq572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq575 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq574
    | (have j0 := eq574 X0 X1
       grind)
    | exact resolve eq574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq576 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq575
    | (have j0 := eq575 X0 X1
       grind)
    | exact resolve eq575 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq649 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 (τ X1) (τ X0)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq105
    | (have j0 := eq105 (τ X1) (τ X0)
       grind)
    | exact resolve eq105 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq649 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq649
    | (have j0 := eq649 X0 X1
       grind)
    | exact resolve eq649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq660 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq656 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq656
    | (have j0 := eq656 X0 X1
       grind)
    | exact resolve eq656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq663 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq660
    | (have j0 := eq660 X0 X1
       grind)
    | exact resolve eq660 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq665 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq663
    | (have j0 := eq663 X0 X1
       grind)
    | exact resolve eq663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq666 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq665
    | (have j0 := eq665 X0 X1
       grind)
    | exact resolve eq665 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq667 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq666
    | (have j0 := eq666 X0 X1
       grind)
    | exact resolve eq666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq743 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq97
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq97 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq744 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq743
  have eq923 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq667 (τ X0) (τ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq667
    | (have j0 := eq667 (τ X0) (τ X1)
       grind)
    | exact resolve eq667 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5453 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq744
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq744
       grind)
    | exact resolve eq13 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5456 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq744
  have eq5457 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5453
  have eq5458 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5457
       have r₂ := eq5456
       grind)
    | exact resolve eq5457 eq5456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5456 eq5457
  have eq5460 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5458
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5458
    | exact resolve eq5458 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5458
  have eq10506 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) X1)) ≠ (σ (M.op (M.op X0 X1) X1)) ∨ (σ X1) = (σ (M.op (M.op X0 X1) X1)) ∨ (σ X1) = (k (σ (M.op (M.op X0 X1) X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (M.op (M.op X0 X1) X1)) (σ X1)
       have i₂ := eq559 X0 X1
       grind)
    | exact superpose eq559 eq13
    | (have j0 := eq13 (σ (M.op (M.op X0 X1) X1)) (σ X1)
       have j1 := eq559 X0 X1
       grind)
    | (have r₁ := eq13 (σ (M.op (M.op X0 X1) X1)) (σ X1)
       have r₂ := eq559 X0 X1
       grind)
    | exact resolve eq13 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10510 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X1 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq559 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq10511 : ∀ X0 X1 : G, (σ X1) = (σ (M.op (M.op X0 X1) X1)) ∨ (σ X1) = (k (σ (M.op (M.op X0 X1) X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq10506 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10506
  have eq10512 : ∀ X0 X1 : G, (σ X1) = (k (σ (M.op (M.op X0 X1) X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq10511 X0 X1
       have j1 := eq10510 X1 X0
       grind)
    | (have r₁ := eq10511 X1 X0
       have r₂ := eq10510 X0 X1
       grind)
    | exact resolve eq10511 eq10510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10511
  have eq10515 : ∀ X0 X1 : G, (σ X1) = (σ (k (M.op (M.op X0 X1) X1) X1)) ∨ (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10512 X0 X1
       have i₂ := eq15 (M.op (M.op X0 X1) X1) X1
       grind)
    | exact superpose eq15 eq10512
    | (have j0 := eq10512 X0 X1
       grind)
    | exact resolve eq10512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10512
  have eq10518 : ∀ X0 X1 : G, (σ X1) = (σ (M.op (M.op X0 X1) X1)) ∨ (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10515 X0 X1
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10515
    | (have j0 := eq10515 X0 X1
       grind)
    | exact resolve eq10515 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10515
  have eq10519 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq10518 X0 X1
       have j1 := eq10510 X1 X0
       grind)
    | (have r₁ := eq10518 X1 X0
       have r₂ := eq10510 X0 X1
       grind)
    | exact resolve eq10518 eq10510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10510 eq10518
  have eq10553 : ∀ X0 X1 : G, (σ (σ (M.op (M.op X1 X0) X0))) = (M.op (σ (σ (M.op (M.op X1 X0) X0))) (σ (M.op (σ X0) (σ (M.op (M.op X1 X0) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq10519 (σ X0) (σ (M.op (M.op X1 X0) X0))
       have i₂ := eq10519 X1 X0
       grind)
    | exact superpose eq10519 eq10519
    | exact resolve eq10519 eq10519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10566 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X0) X0)) = (M.op (σ (M.op (M.op X1 X0) X0)) (M.op (σ X0) (σ (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ (M.op (M.op X1 X0) X0)) (σ X0)
       have i₂ := eq10519 X1 X0
       grind)
    | exact superpose eq10519 eq9
    | exact resolve eq9 eq10519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10578 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X0) X0)) = (M.op (σ (M.op (M.op X1 X0) X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10566 X0 X1
       have i₂ := eq10519 X1 X0
       grind)
    | exact superpose eq10519 eq10566
    | exact resolve eq10566 eq10519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10566
  have eq10582 : ∀ X0 X1 : G, (σ (σ (M.op (M.op X1 X0) X0))) = (M.op (σ (σ (M.op (M.op X1 X0) X0))) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10553 X0 X1
       have i₂ := eq10519 X1 X0
       grind)
    | exact superpose eq10519 eq10553
    | exact resolve eq10553 eq10519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10519 eq10553
  have eq50234 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq5460
       grind)
    | exact superpose eq5460 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq5460
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq5460
       grind)
    | exact resolve eq12 eq5460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5460
  have eq50250 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq50234
  have eq50253 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50250
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq50250
    | exact resolve eq50250 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50250
  have eq51008 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq50253
       grind)
    | exact superpose eq50253 eq10
    | exact resolve eq10 eq50253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50253
  have eq51252 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51008
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq51008
    | exact resolve eq51008 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51008
  have eq51264 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq576 y x
       grind)
    | (have r₁ := eq51252
       have r₂ := eq576 y x
       grind)
    | exact resolve eq51252 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq51252
  have eq51402 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq51264
       grind)
    | exact superpose eq51264 eq10
    | exact resolve eq10 eq51264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51264
  have eq51647 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51402
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq51402
    | exact resolve eq51402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51402
  have eq51648 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq667 y x
       grind)
    | (have r₁ := eq51647
       have r₂ := eq667 y x
       grind)
    | exact resolve eq51647 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq51647
  have eq52122 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq51648
       grind)
    | exact superpose eq51648 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq51648
       grind)
    | exact resolve eq13 eq51648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52130 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10578 y x
       have i₂ := eq51648
       grind)
    | exact superpose eq51648 eq10578
    | exact resolve eq10578 eq51648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52131 : (σ (σ (M.op y y))) = (M.op (σ (σ (M.op y y))) (σ (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10582 y x
       have i₂ := eq51648
       grind)
    | exact superpose eq51648 eq10582
    | exact resolve eq10582 eq51648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10582
  have eq52138 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq52139 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq52122
  have eq52140 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq52139
       have r₂ := eq52138
       grind)
    | exact resolve eq52139 eq52138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52139
  have eq53173 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105 x y
       have i₂ := eq52140
       grind)
    | exact superpose eq52140 eq105
    | (have j0 := eq105 x y
       grind)
    | exact resolve eq105 eq52140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq53191 : (τ x) ≠ (τ x) ∨ (τ y) = (M.op (τ x) (τ y)) ∨ (τ x) = (M.op (τ x) (τ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq923 y x
       have i₂ := eq52140
       grind)
    | exact superpose eq52140 eq923
    | (have j0 := eq923 y x
       grind)
    | exact resolve eq923 eq52140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq53228 : (τ y) = (M.op (τ x) (τ y)) ∨ (τ x) = (M.op (τ x) (τ y)) ∨ x = (M.op x y) := by grind
  clear eq53191
  have eq53236 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq53173
  have eq57868 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ (M.op y y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ (M.op y y))
       have i₂ := eq52130
       grind)
    | exact superpose eq52130 eq12
    | (have j0 := eq12 (σ y) (σ (M.op y y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op y y))
       have r₂ := eq52130
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq52130
       grind)
    | exact resolve eq12 eq52130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52130
  have eq57884 : (σ y) = (k (σ y) (σ (M.op y y))) ∨ x = (M.op x y) := by grind
  clear eq57868
  have eq57888 : (σ y) = (σ (k y (M.op y y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57884
       have i₂ := eq15 y (M.op y y)
       grind)
    | exact superpose eq15 eq57884
    | exact resolve eq57884 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57884
  have eq58439 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (k y (M.op y y)) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq32 (k y (M.op y y)) X0
       have i₂ := eq57888
       grind)
    | exact superpose eq57888 eq32
    | exact resolve eq32 eq57888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57888
  have eq58679 : ∀ X0 : G, (k y (τ X0)) = (k (k y (M.op y y)) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq58439 X0
       have i₂ := eq32 y X0
       grind)
    | exact superpose eq32 eq58439
    | exact resolve eq58439 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq58439
  have eq63442 : ∀ X0 : G, (k y X0) = (k (k y (M.op y y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq58679 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58679
    | exact resolve eq58679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58679
  have eq75004 : (σ (σ (M.op y y))) ≠ (σ (σ (M.op y y))) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ (M.op y y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ (σ y)) (σ (σ (M.op y y)))
       have i₂ := eq52131
       grind)
    | exact superpose eq52131 eq12
    | (have j0 := eq12 (σ (σ y)) (σ (σ (M.op y y)))
       grind)
    | (have r₁ := eq12 (σ (σ y)) (σ (σ (M.op y y)))
       have r₂ := eq52131
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq52131
       grind)
    | exact resolve eq12 eq52131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52131
  have eq75020 : (σ (σ y)) = (k (σ (σ y)) (σ (σ (M.op y y)))) ∨ x = (M.op x y) := by grind
  clear eq75004
  have eq75021 : (σ (σ y)) = (σ (k (σ y) (σ (M.op y y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75020
       have i₂ := eq15 (σ y) (σ (M.op y y))
       grind)
    | exact superpose eq15 eq75020
    | exact resolve eq75020 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75020
  have eq75022 : (σ (σ y)) = (σ (σ (k y (M.op y y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75021
       have i₂ := eq15 y (M.op y y)
       grind)
    | exact superpose eq15 eq75021
    | exact resolve eq75021 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75021
  have eq75586 : ∀ X0 : G, (σ (k (σ (k y (M.op y y))) X0)) = (k (σ (σ y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15 (σ (k y (M.op y y))) X0
       have i₂ := eq75022
       grind)
    | exact superpose eq75022 eq15
    | exact resolve eq15 eq75022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75022
  have eq75913 : ∀ X0 : G, (σ (k (σ y) X0)) = (σ (k (σ (k y (M.op y y))) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq75586 X0
       have i₂ := eq15 (σ y) X0
       grind)
    | exact superpose eq15 eq75586
    | exact resolve eq75586 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75586
  have eq83050 : ∀ X0 : G, (σ (σ (k (k y (M.op y y)) X0))) = (σ (k (σ y) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq75913 (σ X0)
       have i₂ := eq15 (k y (M.op y y)) X0
       grind)
    | exact superpose eq15 eq75913
    | exact resolve eq75913 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75913
  have eq83258 : ∀ X0 : G, (σ (σ (k (k y (M.op y y)) X0))) = (σ (σ (k y X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq83050 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq83050
    | exact resolve eq83050 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83050
  have eq93832 : (τ y) ≠ (τ y) ∨ (τ y) = (τ x) ∨ (τ x) = (k (τ y) (τ x)) ∨ (τ x) = (M.op (τ x) (τ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (τ y) (τ x)
       have i₂ := eq53228
       grind)
    | exact superpose eq53228 eq13
    | (have j0 := eq13 (τ y) (τ x)
       grind)
    | (have r₁ := eq13 (τ y) (τ x)
       have r₂ := eq53228
       grind)
    | exact resolve eq13 eq53228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93845 : (τ y) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ y)) ∨ x = (M.op x y) := by grind
  clear eq53228
  have eq93846 : (τ y) = (τ x) ∨ (τ x) = (k (τ y) (τ x)) ∨ (τ x) = (M.op (τ x) (τ y)) ∨ x = (M.op x y) := by grind
  clear eq93832
  have eq93856 : (τ x) = (k (τ y) (τ x)) ∨ (τ x) = (M.op (τ x) (τ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq93846
       have r₂ := eq93845
       grind)
    | exact resolve eq93846 eq93845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93845 eq93846
  have eq93858 : (τ x) = (M.op (τ x) (τ y)) ∨ (τ (k y x)) = (τ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93856
       have i₂ := eq39 x y
       grind)
    | exact superpose eq39 eq93856
    | exact resolve eq93856 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93856
  have eq94315 : (τ x) ≠ (τ x) ∨ (τ y) = (k (τ y) (τ x)) ∨ (τ (k y x)) = (τ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (τ y) (τ x)
       have i₂ := eq93858
       grind)
    | exact superpose eq93858 eq12
    | (have j0 := eq12 (τ y) (τ x)
       grind)
    | (have r₁ := eq12 (τ y) (τ x)
       have r₂ := eq93858
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq93858
       grind)
    | exact resolve eq12 eq93858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93858
  have eq94329 : (τ y) = (k (τ y) (τ x)) ∨ (τ (k y x)) = (τ x) ∨ x = (M.op x y) := by grind
  clear eq94315
  have eq94341 : (τ (k y x)) = (τ y) ∨ (τ (k y x)) = (τ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94329
       have i₂ := eq39 x y
       grind)
    | exact superpose eq39 eq94329
    | exact resolve eq94329 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94329
  have eq94632 : (k y x) = (σ (τ y)) ∨ (τ (k y x)) = (τ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq94341
       grind)
    | exact superpose eq94341 eq11
    | exact resolve eq11 eq94341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94341
  have eq94782 : y = (k y x) ∨ (τ (k y x)) = (τ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94632
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq94632
    | exact resolve eq94632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94632
  have eq94785 : (τ (k y x)) = (τ x) ∨ y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq94782
       have r₂ := eq12 y x
       grind)
    | exact resolve eq94782 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94782
  have eq95022 : ∀ X0 : G, (τ (k X0 (k y x))) = (k (τ X0) (τ x)) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq39 (k y x) X0
       have i₂ := eq94785
       grind)
    | exact superpose eq94785 eq39
    | exact resolve eq39 eq94785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94785
  have eq95175 : ∀ X0 : G, (τ (k X0 (k y x))) = (τ (k X0 x)) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq95022 X0
       have i₂ := eq39 x X0
       grind)
    | exact superpose eq39 eq95022
    | exact resolve eq95022 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq95022
  have eq96677 : ∀ X0 : G, (k X0 (k y x)) = (σ (τ (k X0 x))) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (k y x))
       have i₂ := eq95175 X0
       grind)
    | exact superpose eq95175 eq11
    | exact resolve eq11 eq95175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95175
  have eq96814 : ∀ X0 : G, (k X0 (k y x)) = (k X0 x) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq96677 X0
       have i₂ := eq11 (k X0 x)
       grind)
    | exact superpose eq11 eq96677
    | exact resolve eq96677 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96677
  have eq97213 : (k y (k y x)) = (k (k y (M.op y y)) x) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq63442 (k y x)
       have i₂ := eq96814 (k y (M.op y y))
       grind)
    | exact superpose eq96814 eq63442
    | exact resolve eq63442 eq96814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63442 eq96814
  have eq97251 : (k y (k y x)) = (k (k y (M.op y y)) x) ∨ y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq97213
       have r₂ := eq12 y x
       grind)
    | exact resolve eq97213 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97213
  have eq102772 : (σ (σ (k y x))) = (σ (σ (k y (k y x)))) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq83258 x
       have i₂ := eq97251
       grind)
    | exact superpose eq97251 eq83258
    | exact resolve eq83258 eq97251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83258 eq97251
  have eq102780 : (σ (σ (k y x))) = (σ (σ (k y (k y x)))) ∨ y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq102772
       have r₂ := eq12 y x
       grind)
    | exact resolve eq102772 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102772
  have eq106339 : (σ (σ x)) = (σ (σ (k y x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102780
       have i₂ := eq52140
       grind)
    | exact superpose eq52140 eq102780
    | exact resolve eq102780 eq52140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52140 eq102780
  have eq106393 : (σ (σ x)) = (σ (σ (k y x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq106339
       have r₂ := eq52138
       grind)
    | exact resolve eq106339 eq52138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106339
  have eq106455 : (σ (k y x)) = (τ (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ (k y x))
       have i₂ := eq106393
       grind)
    | exact superpose eq106393 eq10
    | exact resolve eq10 eq106393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106393
  have eq106609 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106455
       have i₂ := eq10 (σ x)
       grind)
    | exact superpose eq10 eq106455
    | exact resolve eq106455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106455
  have eq141899 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53236
       grind)
    | exact superpose eq53236 eq16
    | exact resolve eq16 eq53236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53236
  have eq141915 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq141899
       have i₂ := eq51648
       grind)
    | exact superpose eq51648 eq141899
    | exact resolve eq141899 eq51648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141899
  have eq141918 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq141915
  have eq141919 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq141918
       have r₂ := eq52138
       grind)
    | exact resolve eq141918 eq52138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141918
  have eq141925 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq141919
       grind)
    | exact superpose eq141919 eq16
    | exact resolve eq16 eq141919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141929 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq141919
       grind)
    | exact superpose eq141919 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq141919
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq141919
       grind)
    | exact resolve eq12 eq141919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141919
  have eq141941 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq141929
  have eq141944 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq141941
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq141941
    | exact resolve eq141941 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141941
  have eq141947 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq141925
       have i₂ := eq51648
       grind)
    | exact superpose eq51648 eq141925
    | exact resolve eq141925 eq51648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51648 eq141925
  have eq141951 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq141947
       have r₂ := eq52138
       grind)
    | exact resolve eq141947 eq52138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52138 eq141947
  have eq141981 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106609
       have i₂ := eq141944
       grind)
    | exact superpose eq141944 eq106609
    | exact resolve eq106609 eq141944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106609 eq141944
  have eq142109 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq141981
  have eq142138 : x = (M.op x y) := by
    first
    | (have r₁ := eq142109
       have r₂ := eq141951
       grind)
    | exact resolve eq142109 eq141951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141951 eq142109
  have eq142353 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq10578 y x
       have i₂ := eq142138
       grind)
    | exact superpose eq142138 eq10578
    | exact resolve eq10578 eq142138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10578
  have eq142371 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq142353
       have i₂ := eq142138
       grind)
    | exact superpose eq142138 eq142353
    | exact resolve eq142353 eq142138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142353
  have eq142485 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq142371
       grind)
    | exact superpose eq142371 eq16
    | exact resolve eq16 eq142371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142371
  have eq142524 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq142485
       have i₂ := eq142138
       grind)
    | exact superpose eq142138 eq142485
    | exact resolve eq142485 eq142138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142138 eq142485
  have eq142525 : False := by grind
  exact eq142525

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pyy_pyx_Equation1043 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1043 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X2)) X0 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq70 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
       have i₂ := eq24 X0 X1 X3 X4
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq256 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq10
    | (have j1 := eq52 X1 X0
       grind)
    | exact resolve eq10 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq267 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq256 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq256
    | (have j0 := eq256 X0 X1
       grind)
    | exact resolve eq256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq728 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 X0 x X0
       have i₂ := eq76 X0 X0 x
       grind)
    | exact superpose eq76 eq24
    | exact resolve eq24 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq772 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq76 X0 X0 X0
       have i₂ := eq728 X0
       grind)
    | exact superpose eq728 eq76
    | exact resolve eq76 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq851 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq926 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq851
    | (have j0 := eq851 (M.op X1 X1) X1
       grind)
    | exact resolve eq851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq1009 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq772 X0
       grind)
    | exact superpose eq772 eq76
    | exact resolve eq76 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1012 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1009 X0 X1
       have i₂ := eq25 X0 X1 X0
       grind)
    | exact superpose eq25 eq1009
    | exact resolve eq1009 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1009
  have eq1633 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1012 X0 X1
       grind)
    | exact superpose eq1012 eq9
    | exact resolve eq9 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1656 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1633 X0 X1
       have i₂ := eq772 X0
       grind)
    | exact superpose eq772 eq1633
    | exact resolve eq1633 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq1633
  have eq1789 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1656 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1656
    | exact resolve eq1656 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2041 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq267 y x
       grind)
    | exact superpose eq267 eq16
    | (have j1 := eq267 y x
       grind)
    | exact resolve eq16 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq42246 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2041
       have i₂ := eq926 x y
       grind)
    | exact superpose eq926 eq2041
    | (have j1 := eq926 (M.op y y) y
       grind)
    | (have r₁ := eq2041
       have r₂ := eq926 x y
       grind)
    | (have r₁ := eq2041
       have r₂ := eq926 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2041
       have r₂ := eq926 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2041 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926 eq2041
  have eq42247 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq42246
  have eq42248 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq42247
  have eq42300 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1656 y X0
       have i₂ := eq42248
       grind)
    | exact superpose eq42248 eq1656
    | exact resolve eq1656 eq42248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656
  have eq42301 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1789 y X0
       have i₂ := eq42248
       grind)
    | exact superpose eq42248 eq1789
    | exact resolve eq1789 eq42248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq42248
  have eq44265 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq42301 (σ x)
       grind)
    | exact superpose eq42301 eq16
    | exact resolve eq16 eq42301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42301
  have eq49910 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq44265
       have i₂ := eq42300 x
       grind)
    | exact superpose eq42300 eq44265
    | exact resolve eq44265 eq42300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42300 eq44265
  have eq49911 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq49910
  have eq49912 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq49911
  have eq50419 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq49912
       grind)
    | exact superpose eq49912 eq10
    | exact resolve eq10 eq49912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49912
  have eq50505 : x = y ∨ x = y := by
    first
    | (have i₁ := eq50419
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq50419
    | exact resolve eq50419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50419
  have eq50506 : x = y := by grind
  clear eq50505
  have eq50919 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50506
       grind)
    | exact superpose eq50506 eq16
    | exact resolve eq16 eq50506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50506
  have eq50920 : False := by grind
  exact eq50920

/-- `Equation1053`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyx_pxy_Equation1053 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1053 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1053.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X1 X2)) X2)
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2))) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq26 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq26
    | exact resolve eq26 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq75 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq27
    | exact resolve eq27 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq10
    | (have j1 := eq54 X1 X0
       grind)
    | exact resolve eq10 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq192
    | (have j0 := eq192 X0 X1
       grind)
    | exact resolve eq192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq983 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1044 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq983 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq983
    | (have j0 := eq983 (M.op X1 X1) X1
       grind)
    | exact resolve eq983 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq1882 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
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
  have eq20186 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1882
       have i₂ := eq1044 x y
       grind)
    | exact superpose eq1044 eq1882
    | (have j1 := eq1044 (M.op y y) y
       grind)
    | (have r₁ := eq1882
       have r₂ := eq1044 x y
       grind)
    | (have r₁ := eq1882
       have r₂ := eq1044 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1882
       have r₂ := eq1044 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1882 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq1882
  have eq20187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20186
  have eq20188 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20187
  have eq20195 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27 y X0
       have i₂ := eq20188
       grind)
    | exact superpose eq20188 eq27
    | exact resolve eq27 eq20188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq20199 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq75 y X0
       have i₂ := eq20188
       grind)
    | exact superpose eq20188 eq75
    | exact resolve eq75 eq20188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq20188
  have eq21266 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq20199 (σ x)
       grind)
    | exact superpose eq20199 eq16
    | exact resolve eq16 eq20199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20199
  have eq23053 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21266
       have i₂ := eq20195 x
       grind)
    | exact superpose eq20195 eq21266
    | exact resolve eq21266 eq20195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20195 eq21266
  have eq23054 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23053
  have eq23055 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq23054
  have eq23363 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23055
       grind)
    | exact superpose eq23055 eq10
    | exact resolve eq10 eq23055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23055
  have eq23429 : x = y ∨ x = y := by
    first
    | (have i₁ := eq23363
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23363
    | exact resolve eq23363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23363
  have eq23430 : x = y := by grind
  clear eq23429
  have eq23739 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23430
       grind)
    | exact superpose eq23430 eq16
    | exact resolve eq16 eq23430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23430
  have eq23742 : False := by grind
  exact eq23742

/-- `Equation1112`: `x = y ◇ ((y ◇ (x ◇ y)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation1112 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1112 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1112.models_iff G M).mp hM
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq47 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq48 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq116 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq386 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq417 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq386
    | (have j0 := eq386 X0 X1
       grind)
    | exact resolve eq386 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq862 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq116
       have i₂ := eq417 y x
       grind)
    | exact superpose eq417 eq116
    | (have j1 := eq417 (σ y) (σ x)
       grind)
    | (have r₁ := eq116
       have r₂ := eq417 y x
       grind)
    | (have r₁ := eq116
       have r₂ := eq417 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq116
       have r₂ := eq417 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq116 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq863 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq862
  have eq8877 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq863
       grind)
    | exact superpose eq863 eq16
    | exact resolve eq16 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8882 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq863
       grind)
    | exact superpose eq863 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq863
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq863
       grind)
    | exact resolve eq13 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq8884 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8882
  have eq8885 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8884
  have eq8887 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8885
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8885
    | exact resolve eq8885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8885
  have eq9246 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq417 y x
       have i₂ := eq8887
       grind)
    | exact superpose eq8887 eq417
    | (have j0 := eq417 y x
       grind)
    | exact resolve eq417 eq8887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq9247 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq8887
       grind)
    | exact superpose eq8887 eq10
    | exact resolve eq10 eq8887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8887
  have eq9303 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq9246
  have eq9342 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq9247
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9247
    | exact resolve eq9247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9247
  have eq9343 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9303
       have r₂ := eq8877
       grind)
    | exact resolve eq9303 eq8877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8877 eq9303
  have eq9346 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x (k y x)
       grind)
    | (have r₁ := eq9342
       have r₂ := eq13 y x
       grind)
    | exact resolve eq9342 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9342
  have eq9635 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq120 x y
       have i₂ := eq9346
       grind)
    | exact superpose eq9346 eq120
    | (have j0 := eq120 x y
       grind)
    | exact resolve eq120 eq9346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq9346
  have eq9661 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9635
  have eq9662 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9661
  have eq10049 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq9662
       grind)
    | exact superpose eq9662 eq16
    | exact resolve eq16 eq9662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9662
  have eq10571 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10049
       have i₂ := eq9343
       grind)
    | exact superpose eq9343 eq10049
    | exact resolve eq10049 eq9343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9343 eq10049
  have eq10572 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10571
  have eq10573 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq10572
  have eq10726 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10573
       grind)
    | exact superpose eq10573 eq10
    | exact resolve eq10 eq10573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10573
  have eq10816 : x = y ∨ x = y := by
    first
    | (have i₁ := eq10726
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10726
    | exact resolve eq10726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10726
  have eq10817 : x = y := by grind
  clear eq10816
  have eq10990 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10817
       grind)
    | exact superpose eq10817 eq16
    | exact resolve eq16 eq10817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10817
  have eq10991 : False := by grind
  exact eq10991

/-- `Equation1184`: `x = y ◇ ((z ◇ (z ◇ y)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1184 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1184 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1184.models_iff G M).mp hM
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
  have eq46 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq156 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq2526 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq2578 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2526 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2526
    | (have j0 := eq2526 X0 X1
       grind)
    | exact resolve eq2526 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526
  have eq3248 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq156
       have i₂ := eq2578 y x
       grind)
    | exact superpose eq2578 eq156
    | (have j1 := eq2578 (σ y) (σ x)
       grind)
    | (have r₁ := eq156
       have r₂ := eq2578 y x
       grind)
    | (have r₁ := eq156
       have r₂ := eq2578 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq156
       have r₂ := eq2578 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq156 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq3249 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3248
  have eq44161 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3249
       grind)
    | exact superpose eq3249 eq16
    | exact resolve eq16 eq3249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44179 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3249
       grind)
    | exact superpose eq3249 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3249
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3249
       grind)
    | exact resolve eq13 eq3249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249
  have eq44248 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq44179
  have eq44249 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq44248
  have eq44305 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq44249
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq44249
    | exact resolve eq44249 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44249
  have eq44863 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2578 y x
       have i₂ := eq44305
       grind)
    | exact superpose eq44305 eq2578
    | (have j0 := eq2578 y x
       grind)
    | exact resolve eq2578 eq44305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq44864 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq44305
       grind)
    | exact superpose eq44305 eq10
    | exact resolve eq10 eq44305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44305
  have eq44931 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq44863
  have eq44961 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq44864
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq44864
    | exact resolve eq44864 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44864
  have eq44962 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq44931
       have r₂ := eq44161
       grind)
    | exact resolve eq44931 eq44161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44161 eq44931
  have eq44965 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq44961
       have r₂ := eq13 x y
       grind)
    | exact resolve eq44961 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44961
  have eq45418 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq162 x y
       have i₂ := eq44965
       grind)
    | exact superpose eq44965 eq162
    | (have j0 := eq162 x y
       grind)
    | exact resolve eq162 eq44965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq44965
  have eq45442 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45418
  have eq45443 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45442
  have eq45549 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq45443
       grind)
    | exact superpose eq45443 eq16
    | exact resolve eq16 eq45443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45443
  have eq45809 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45549
       have i₂ := eq44962
       grind)
    | exact superpose eq44962 eq45549
    | exact resolve eq45549 eq44962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44962 eq45549
  have eq45810 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45809
  have eq45811 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq45810
  have eq45988 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq45811
       grind)
    | exact superpose eq45811 eq10
    | exact resolve eq10 eq45811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45811
  have eq46079 : x = y ∨ x = y := by
    first
    | (have i₁ := eq45988
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq45988
    | exact resolve eq45988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45988
  have eq46080 : x = y := by grind
  clear eq46079
  have eq46260 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46080
       grind)
    | exact superpose eq46080 eq16
    | exact resolve eq16 eq46080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46080
  have eq46261 : False := by grind
  exact eq46261

/-- `Equation1229`: `x = x ◇ (((x ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1229 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1229 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1229.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq110 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq16
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq441 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq118 (τ X0) (τ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq118
    | (have j0 := eq118 (τ X0) (τ X1)
       grind)
    | exact resolve eq118 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq441
    | (have j0 := eq441 X0 X1
       grind)
    | exact resolve eq441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq451 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq448
    | (have j0 := eq448 X0 X1
       grind)
    | exact resolve eq448 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq453 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq451
    | (have j0 := eq451 X0 X1
       grind)
    | exact resolve eq451 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq454 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq453
    | (have j0 := eq453 X0 X1
       grind)
    | exact resolve eq453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq455 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq454
    | (have j0 := eq454 X0 X1
       grind)
    | exact resolve eq454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq456 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq455
    | (have j0 := eq455 X0 X1
       grind)
    | exact resolve eq455 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq471 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq119 (τ X0) (τ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq119
    | (have j0 := eq119 (τ X0) (τ X1)
       grind)
    | exact resolve eq119 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq479 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq471
    | (have j0 := eq471 X0 X1
       grind)
    | exact resolve eq471 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq482 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq479 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq479
    | (have j0 := eq479 X0 X1
       grind)
    | exact resolve eq479 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq484 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq482 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq482
    | (have j0 := eq482 X0 X1
       grind)
    | exact resolve eq482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq485 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq484
    | (have j0 := eq484 X0 X1
       grind)
    | exact resolve eq484 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq486 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq485
    | (have j0 := eq485 X0 X1
       grind)
    | exact resolve eq485 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq487 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq486
    | (have j0 := eq486 X0 X1
       grind)
    | exact resolve eq486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq498 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq110
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq110 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq498
  have eq3834 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq499
       grind)
    | exact superpose eq499 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq499
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq499
       grind)
    | exact resolve eq12 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq3846 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3834
  have eq3848 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3846
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3846
    | exact resolve eq3846 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3846
  have eq22451 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3848
       grind)
    | exact superpose eq3848 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3848
       grind)
    | exact resolve eq12 eq3848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22452 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3848
       grind)
    | exact superpose eq3848 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3848
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3848
       grind)
    | exact resolve eq13 eq3848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3848
  have eq22471 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq22452
  have eq22478 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22471
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22471
    | exact resolve eq22471 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22471
  have eq22479 : (σ x) = (σ (k x y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22451
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22451
    | exact resolve eq22451 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22451
  have eq22480 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq22479
  have eq94467 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq22478
       grind)
    | exact superpose eq22478 eq10
    | exact resolve eq10 eq22478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22478
  have eq94508 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq94467
       have r₂ := eq22480
       grind)
    | exact resolve eq94467 eq22480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22480 eq94467
  have eq94526 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94508
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq94508
    | exact resolve eq94508 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94508
  have eq94527 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq487 x y
       grind)
    | (have r₁ := eq94526
       have r₂ := eq487 x y
       grind)
    | exact resolve eq94526 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq94526
  have eq95110 : (k x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq94527
       grind)
    | exact superpose eq94527 eq10
    | exact resolve eq10 eq94527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94527
  have eq95286 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq95110
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq95110
    | exact resolve eq95110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95110
  have eq95287 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq456 x y
       grind)
    | (have r₁ := eq95286
       have r₂ := eq456 x y
       grind)
    | exact resolve eq95286 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq95286
  have eq95831 : y ≠ y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq95287
       grind)
    | exact superpose eq95287 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq95287
       grind)
    | exact resolve eq12 eq95287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95858 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq95859 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq95831
  have eq96330 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118 x y
       have i₂ := eq95859
       grind)
    | exact superpose eq95859 eq118
    | (have j0 := eq118 x y
       grind)
    | exact resolve eq118 eq95859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq96541 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq96330
  have eq102267 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96541
       grind)
    | exact superpose eq96541 eq16
    | exact resolve eq16 eq96541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96541
  have eq102767 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102267
       have i₂ := eq95287
       grind)
    | exact superpose eq95287 eq102267
    | exact resolve eq102267 eq95287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102267
  have eq102770 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq102767
  have eq102771 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq102770
       have r₂ := eq95858
       grind)
    | exact resolve eq102770 eq95858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102770
  have eq103033 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq102771
       grind)
    | exact superpose eq102771 eq16
    | exact resolve eq16 eq102771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103041 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq102771
       grind)
    | exact superpose eq102771 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq102771
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq102771
       grind)
    | exact resolve eq13 eq102771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102771
  have eq103053 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq103041
  have eq103061 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103053
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq103053
    | exact resolve eq103053 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103053
  have eq103323 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103033
       have i₂ := eq95287
       grind)
    | exact superpose eq95287 eq103033
    | exact resolve eq103033 eq95287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95287 eq103033
  have eq103327 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq103323
       have r₂ := eq95858
       grind)
    | exact resolve eq103323 eq95858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95858 eq103323
  have eq103597 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103061
       have i₂ := eq95859
       grind)
    | exact superpose eq95859 eq103061
    | exact resolve eq103061 eq95859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95859 eq103061
  have eq103746 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq103597
  have eq103845 : x = (M.op x y) := by
    first
    | (have r₁ := eq103746
       have r₂ := eq103327
       grind)
    | exact resolve eq103746 eq103327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103327 eq103746
  have eq104157 : x ≠ y ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq103845
       grind)
    | exact superpose eq103845 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq103845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104158 : x ≠ x ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq103845
       grind)
    | exact superpose eq103845 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq103845
       grind)
    | exact resolve eq13 eq103845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104187 : y = (k x y) ∨ x = y := by grind
  clear eq104158
  have eq104871 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq119 x y
       have i₂ := eq104187
       grind)
    | exact superpose eq104187 eq119
    | (have j0 := eq119 x y
       grind)
    | exact resolve eq119 eq104187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq104980 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq104871
  have eq108749 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq104980
       grind)
    | exact superpose eq104980 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq104980
       grind)
    | exact resolve eq12 eq104980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104980
  have eq108755 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq108749
  have eq108757 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq108755
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq108755
    | exact resolve eq108755 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108755
  have eq109389 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq108757
       grind)
    | exact superpose eq108757 eq16
    | exact resolve eq16 eq108757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108757
  have eq109406 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq109389
       have i₂ := eq103845
       grind)
    | exact superpose eq103845 eq109389
    | exact resolve eq109389 eq103845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109389
  have eq109407 : (σ x) = (σ (k x y)) ∨ x = y := by grind
  clear eq109406
  have eq109732 : (k x y) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq109407
       grind)
    | exact superpose eq109407 eq10
    | exact resolve eq10 eq109407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109407
  have eq109900 : x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq109732
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq109732
    | exact resolve eq109732 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109732
  have eq109901 : x = (k x y) := by
    first
    | (have r₁ := eq109900
       have r₂ := eq104157
       grind)
    | exact resolve eq109900 eq104157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104157 eq109900
  have eq110183 : x = y ∨ x = y := by
    first
    | (have i₁ := eq104187
       have i₂ := eq109901
       grind)
    | exact superpose eq109901 eq104187
    | exact resolve eq104187 eq109901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104187
  have eq110300 : x = y := by grind
  clear eq110183
  have eq110510 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110300
       grind)
    | exact superpose eq110300 eq16
    | exact resolve eq16 eq110300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110511 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq110300
       grind)
    | exact superpose eq110300 eq110
    | exact resolve eq110 eq110300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq110544 : x = (M.op x x) := by
    first
    | (have i₁ := eq103845
       have i₂ := eq110300
       grind)
    | exact superpose eq110300 eq103845
    | exact resolve eq103845 eq110300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103845
  have eq110551 : x = (k x x) := by
    first
    | (have i₁ := eq109901
       have i₂ := eq110300
       grind)
    | exact superpose eq110300 eq109901
    | exact resolve eq109901 eq110300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109901 eq110300
  have eq110578 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq110511
  have eq110580 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq110578
       have i₂ := eq110544
       grind)
    | exact superpose eq110544 eq110578
    | exact resolve eq110578 eq110544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110578
  have eq110581 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq110510
       have i₂ := eq110544
       grind)
    | exact superpose eq110544 eq110510
    | exact resolve eq110510 eq110544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110510 eq110544
  have eq110582 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq110580
       have i₂ := eq110551
       grind)
    | exact superpose eq110551 eq110580
    | exact resolve eq110580 eq110551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110551 eq110580
  have eq110583 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq110582
  have eq110584 : False := by grind
  exact eq110584

/-- `Equation1229`: `x = x ◇ (((x ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1229 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1229 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1229.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq101 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq419 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq450 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq419
    | (have j0 := eq419 X0 X1
       grind)
    | exact resolve eq419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq924 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq450 y x
       grind)
    | exact superpose eq450 eq101
    | (have j1 := eq450 (σ y) (σ x)
       grind)
    | (have r₁ := eq101
       have r₂ := eq450 y x
       grind)
    | (have r₁ := eq101
       have r₂ := eq450 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq101
       have r₂ := eq450 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq101 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq925 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq924
  have eq10711 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq925
       grind)
    | exact superpose eq925 eq16
    | exact resolve eq16 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10715 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq925
       grind)
    | exact superpose eq925 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq925
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq925
       grind)
    | exact resolve eq13 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq10723 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10715
  have eq10724 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10723
  have eq10733 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10724
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq10724
    | exact resolve eq10724 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10724
  have eq11291 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq450 y x
       have i₂ := eq10733
       grind)
    | exact superpose eq10733 eq450
    | (have j0 := eq450 y x
       grind)
    | exact resolve eq450 eq10733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq10733
  have eq11351 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11291
  have eq11392 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11351
       have r₂ := eq10711
       grind)
    | exact resolve eq11351 eq10711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10711 eq11351
  have eq11561 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq11392
       grind)
    | exact superpose eq11392 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq11392
       grind)
    | exact resolve eq13 eq11392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11569 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq11561
  have eq11570 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11569
  have eq11670 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq106 x y
       have i₂ := eq11570
       grind)
    | exact superpose eq11570 eq106
    | (have j0 := eq106 x y
       grind)
    | exact resolve eq106 eq11570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq11570
  have eq11696 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11670
  have eq11697 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11696
  have eq11921 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq11697
       grind)
    | exact superpose eq11697 eq16
    | exact resolve eq16 eq11697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11697
  have eq12187 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11921
       have i₂ := eq11392
       grind)
    | exact superpose eq11392 eq11921
    | exact resolve eq11921 eq11392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11392 eq11921
  have eq12188 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12187
  have eq12189 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq12188
  have eq12268 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12189
       grind)
    | exact superpose eq12189 eq10
    | exact resolve eq10 eq12189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12189
  have eq12362 : x = y ∨ x = y := by
    first
    | (have i₁ := eq12268
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12268
    | exact resolve eq12268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12268
  have eq12363 : x = y := by grind
  clear eq12362
  have eq12436 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12363
       grind)
    | exact superpose eq12363 eq16
    | exact resolve eq16 eq12363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12363
  have eq12437 : False := by grind
  exact eq12437
