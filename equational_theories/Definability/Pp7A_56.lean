import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation3112 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  clear eq18
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
  have eq114 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  clear eq19
  have eq115 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq612 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq114 X1 X0
       grind)
    | exact superpose eq114 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq114 X1 X0
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq114 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq114 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq13 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq617 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq612 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq618 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq617 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq698 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq2159 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq618 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq618
    | exact resolve eq618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq2201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2159 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2159
    | (have j0 := eq2159 X0 X1
       grind)
    | exact resolve eq2159 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2159
  have eq2237 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2201 X0 X1
       grind)
    | exact superpose eq2201 eq10
    | (have j1 := eq2201 X0 X1
       grind)
    | exact resolve eq10 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2278 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2237 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2237
    | (have j0 := eq2237 X0 X1
       grind)
    | exact resolve eq2237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237
  have eq2293 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq2278 (σ X0) X1
       grind)
    | exact superpose eq2278 eq28
    | (have j1 := eq2278 (σ X0) X1
       grind)
    | exact resolve eq28 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2278
  have eq4030 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2293 X1 (σ X0)
       grind)
    | exact superpose eq2293 eq37
    | (have j1 := eq2293 X1 (σ X0)
       grind)
    | exact resolve eq37 eq2293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2293
  have eq4095 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4030 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4030
    | (have j0 := eq4030 X0 X1
       grind)
    | exact resolve eq4030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030
  have eq4127 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4095 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4095
    | (have j0 := eq4095 X0 X1
       grind)
    | exact resolve eq4095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095
  have eq4137 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4127 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4127
    | (have j0 := eq4127 X0 X1
       grind)
    | exact resolve eq4127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127
  have eq4341 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4137 X0 X1
       grind)
    | exact superpose eq4137 eq11
    | (have j1 := eq4137 X0 X1
       grind)
    | exact resolve eq11 eq4137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq5209 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4341 y x
       grind)
    | exact superpose eq4341 eq16
    | (have j1 := eq4341 y x
       grind)
    | exact resolve eq16 eq4341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq5236 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5209
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5209
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5209
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5209
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5209 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5237 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5209
       have i₂ := eq2201 x y
       grind)
    | exact superpose eq2201 eq5209
    | (have j1 := eq2201 x y
       grind)
    | (have r₁ := eq5209
       have r₂ := eq2201 x y
       grind)
    | (have r₁ := eq5209
       have r₂ := eq2201 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5209
       have r₂ := eq2201 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5209 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201 eq5209
  have eq5240 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5237
  have eq5241 : x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq5240
  have eq5242 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5236
  have eq5243 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq5242
  have eq5247 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5241
       grind)
    | exact superpose eq5241 eq16
    | exact resolve eq16 eq5241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5241
  have eq5248 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5247
       have r₂ := eq22 x
       grind)
    | exact resolve eq5247 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5247
  have eq5253 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq698 x y
       have i₂ := eq5248
       grind)
    | exact superpose eq5248 eq698
    | (have j0 := eq698 x y
       grind)
    | exact resolve eq698 eq5248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq5248
  have eq5259 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5253
  have eq5260 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5259
  have eq5264 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5243
       grind)
    | exact superpose eq5243 eq16
    | exact resolve eq16 eq5243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5243
  have eq5265 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5264
       have r₂ := eq22 x
       grind)
    | exact resolve eq5264 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5264
  have eq5276 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5260
       grind)
    | exact superpose eq5260 eq16
    | exact resolve eq16 eq5260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5260
  have eq5296 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5276
       have i₂ := eq5265
       grind)
    | exact superpose eq5265 eq5276
    | exact resolve eq5276 eq5265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5265 eq5276
  have eq5297 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq5296
  have eq5298 : (σ x) = (σ y) := by grind
  clear eq5297
  have eq5299 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5298
       grind)
    | exact superpose eq5298 eq16
    | exact resolve eq16 eq5298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5300 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5298
       grind)
    | exact superpose eq5298 eq10
    | exact resolve eq10 eq5298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5298
  have eq5351 : x = y := by
    first
    | (have i₁ := eq5300
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5300
    | exact resolve eq5300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5300
  have eq5352 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5299
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5299
    | exact resolve eq5299 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5299
  have eq5353 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5352
       have i₂ := eq5351
       grind)
    | exact superpose eq5351 eq5352
    | exact resolve eq5352 eq5351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5351 eq5352
  have eq5354 : False := by grind
  exact eq5354

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq83 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
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
  have eq102 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq109 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq110 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq112 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq109
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq120
    | exact resolve eq120 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq121
    | exact resolve eq121 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq128 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq102 (τ X0)
       grind)
    | exact superpose eq102 eq35
    | (have j1 := eq102 (τ X0)
       grind)
    | exact resolve eq35 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq102
  have eq310 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq59 (τ X0) (τ X0)
       grind)
    | exact superpose eq59 eq300
    | (have j0 := eq300 X0
       grind)
    | exact resolve eq300 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq300
  have eq382 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq759 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq772 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq759 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq759 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq759 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq759 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq781 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq772
    | (have j0 := eq772 X0 X1
       grind)
    | exact resolve eq772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq836 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ x) X0 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq5764 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq83
    | (have j0 := eq83 x
       grind)
    | exact resolve eq83 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq5794 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5764
  have eq5799 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5794
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5794
    | exact resolve eq5794 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5794
  have eq5816 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5799
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5799 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5799
  have eq5820 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5816 eq50
    | exact resolve eq50 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq5816
  have eq6027 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq112 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq112
    | (have j0 := eq112 y
       grind)
    | exact resolve eq112 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq6056 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6027
  have eq6060 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6056
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq6056
    | exact resolve eq6056 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq6056
  have eq6084 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6060
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6060 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6060
  have eq6104 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6084 eq128
    | exact resolve eq128 eq6084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq6084
  have eq7539 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq382 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq310 (σ X0)
       grind)
    | exact superpose eq310 eq382
    | (have j1 := eq310 (σ X0)
       grind)
    | exact resolve eq382 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310 eq382
  have eq7543 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7539 X0
       have i₂ := eq16 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq16 eq7539
    | (have j0 := eq7539 X0
       grind)
    | exact resolve eq7539 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7539
  have eq7584 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7543 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq7543
    | (have j0 := eq7543 X0
       grind)
    | exact resolve eq7543 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7543
  have eq7600 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7584 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq7584
    | (have j0 := eq7584 X0
       grind)
    | exact resolve eq7584 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7584
  have eq7603 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7600 X0
       have j1 := eq67 X0 X0
       grind)
    | (have r₁ := eq7600 x
       have r₂ := eq67 x x
       grind)
    | exact resolve eq7600 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq7600
  have eq8957 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq781 X0 (M.op X0 X0)
       have i₂ := eq7603 X0
       grind)
    | exact superpose eq7603 eq781
    | (have j0 := eq781 X0 (M.op X0 X0)
       grind)
    | exact resolve eq781 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq7603
  have eq9063 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8957 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8957
  have eq9064 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq9063 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9063
  have eq9564 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9064 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9064
    | (have j0 := eq9064 x
       grind)
    | exact resolve eq9064 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9565 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9064 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9064
    | (have j0 := eq9064 y
       grind)
    | exact resolve eq9064 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9575 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq55 (σ X0) (σ X0)
       have i₂ := eq9064 X0
       grind)
    | exact superpose eq9064 eq55
    | exact resolve eq55 eq9064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9064
  have eq9642 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq9564
       grind)
    | exact superpose eq9564 eq16
    | exact resolve eq16 eq9564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9670 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq5820 eq9642
    | exact resolve eq9642 eq5820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9642
  have eq9776 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq9565
       grind)
    | exact superpose eq9565 eq16
    | exact resolve eq16 eq9565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9565
  have eq9804 : (M.op y y) = (k y y) := by
    first
    | exact superpose eq6104 eq9776
    | exact resolve eq9776 eq6104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9776
  have eq21685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq21695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq21685
    | exact resolve eq21685 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21685
  have eq21707 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq21695
       have r₂ := eq28
       grind)
    | exact resolve eq21695 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21695
  have eq21711 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq21707
    | exact resolve eq21707 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21707
  have eq21713 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21711 eq6104
    | exact resolve eq6104 eq21711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6104 eq21711
  have eq21777 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21713
       have i₂ := eq9804
       grind)
    | exact superpose eq9804 eq21713
    | exact resolve eq21713 eq9804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9804 eq21713
  have eq21782 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq21777
    | exact resolve eq21777 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21777
  have eq21783 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21782
  have eq21794 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9575 y
       have i₂ := eq21783
       grind)
    | exact superpose eq21783 eq9575
    | exact resolve eq9575 eq21783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9575
  have eq21801 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq55 y y
       have i₂ := eq21783
       grind)
    | exact superpose eq21783 eq55
    | exact resolve eq55 eq21783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq21783
  have eq21841 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21801
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21801
    | exact resolve eq21801 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21801
  have eq21843 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21794
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21794
    | exact resolve eq21794 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21794
  have eq21851 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21843
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21843
    | exact resolve eq21843 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21843
  have eq21855 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq21851
    | exact resolve eq21851 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21851
  have eq21858 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21841 eq57
    | exact resolve eq57 eq21841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21841
  have eq21900 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21855 eq28
    | exact resolve eq28 eq21855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21855
  have eq22183 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21858 eq5820
    | exact resolve eq5820 eq21858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5820 eq21858
  have eq22275 : (τ (σ x)) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22183
       have i₂ := eq9670
       grind)
    | exact superpose eq9670 eq22183
    | exact resolve eq22183 eq9670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9670 eq22183
  have eq22291 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq22275
    | exact resolve eq22275 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22275
  have eq24454 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq836 x
       have i₂ := eq22291
       grind)
    | exact superpose eq22291 eq836
    | exact resolve eq836 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22291
  have eq24534 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56 eq24454
    | exact resolve eq24454 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24454
  have eq24554 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24534
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24534
    | exact resolve eq24534 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24534
  have eq24555 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq24554
  have eq24565 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24555 eq21
    | exact resolve eq21 eq24555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24555
  have eq24714 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24565
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24565
    | exact resolve eq24565 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24565
  have eq24843 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24714 eq21900
    | (have r₁ := eq21900
       have r₂ := eq24714
       grind)
    | exact resolve eq21900 eq24714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21900
  have eq24853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24843
  have eq24854 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24853
  have eq24971 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24854 eq57
    | exact resolve eq57 eq24854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24854
  have eq25126 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24971 eq840
    | exact resolve eq840 eq24971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq24971
  have eq25206 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57 eq25126
    | exact resolve eq25126 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq25126
  have eq25225 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq25206
    | exact resolve eq25206 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25206
  have eq25239 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25225 eq28
    | exact resolve eq28 eq25225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25225
  have eq25274 : x = (M.op x y) := by
    first
    | (have r₁ := eq25239
       have r₂ := eq24714
       grind)
    | exact resolve eq25239 eq24714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24714 eq25239
  have eq25279 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq25274 eq21
    | exact resolve eq21 eq25274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq25282 : x = (M.op x x) := by
    first
    | exact superpose eq25274 eq56
    | exact resolve eq56 eq25274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25441 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25279
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25279
    | exact resolve eq25279 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25279
  have eq25490 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq25441 eq27
    | exact resolve eq27 eq25441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq25734 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9564
       have i₂ := eq25282
       grind)
    | exact superpose eq25282 eq9564
    | exact resolve eq9564 eq25282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9564
  have eq25740 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq836 x
       have i₂ := eq25282
       grind)
    | exact superpose eq25282 eq836
    | exact resolve eq836 eq25282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq25282
  have eq25820 : y = (M.op x y) := by
    first
    | exact superpose eq56 eq25740
    | exact resolve eq25740 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq25740
  have eq25826 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq25441 eq25734
    | exact resolve eq25734 eq25441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25734
  have eq25840 : y = (M.op x y) := by
    first
    | (have i₁ := eq25820
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25820
    | exact resolve eq25820 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25820
  have eq25846 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq25826
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25826
    | exact resolve eq25826 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25826
  have eq25853 : x = y := by
    first
    | exact superpose eq25274 eq25840
    | exact resolve eq25840 eq25274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25274 eq25840
  have eq25859 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq25441 eq25846
    | exact resolve eq25846 eq25441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25846
  have eq25876 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq25853
       grind)
    | exact superpose eq25853 eq25
    | exact resolve eq25 eq25853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq25853
  have eq26022 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25876
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25876
    | exact resolve eq25876 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq25876
  have eq26086 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25441 eq26022
    | exact resolve eq26022 eq25441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25441 eq26022
  have eq26926 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26086 eq25490
    | exact resolve eq25490 eq26086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25490 eq26086
  have eq27209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25859 eq26926
    | exact resolve eq26926 eq25859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25859 eq26926
  have eq27210 : False := by grind
  exact eq27210

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_x_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ x) (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op X0 X1) X0
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : x ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq63 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq64 eq61
    | exact resolve eq61 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq80 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq82 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq80
  have eq88 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq73 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq89 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq63 eq89
    | exact resolve eq89 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq94
    | exact resolve eq94 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq63 eq95
    | exact resolve eq95 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq109 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq110 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq109
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq120
    | exact resolve eq120 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq121
    | exact resolve eq121 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq110
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq123
  have eq260 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq97 (τ X0)
       grind)
    | exact superpose eq97 eq35
    | (have j1 := eq97 (τ X0)
       grind)
    | exact resolve eq35 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq97
  have eq355 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq559 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X1) (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq61
    | (have j1 := eq76 X0 X1
       grind)
    | exact resolve eq61 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq798 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq68 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68
    | (have j0 := eq68 x X0 y
       grind)
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq68
    | (have j0 := eq68 (σ x) X0 (σ y)
       grind)
    | exact resolve eq68 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq8043 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq564 x y
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq564
    | (have j0 := eq564 x y
       grind)
    | exact resolve eq564 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq8082 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8043
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8043
    | exact resolve eq8043 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8043
  have eq8170 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8082
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8082
    | exact resolve eq8082 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8082
  have eq8254 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8170
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8170
    | exact resolve eq8170 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8170
  have eq8336 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8254
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8254
    | exact resolve eq8254 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8254
  have eq8417 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8336
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8336
    | exact resolve eq8336 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8336
  have eq8484 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8417
    | exact resolve eq8417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8417
  have eq9502 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq96 eq93
    | exact resolve eq93 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq96
  have eq9517 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq29 eq9502
    | exact resolve eq9502 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9502
  have eq9520 : (M.op x y) = (M.op x x) ∨ x = (k x (M.op x y)) := by
    first
    | (have r₁ := eq9517
       have r₂ := eq72
       grind)
    | exact resolve eq9517 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9517
  have eq9521 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq9520
       grind)
    | exact superpose eq9520 eq82
    | exact resolve eq82 eq9520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq9520
  have eq9569 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | (have r₁ := eq9521
       have r₂ := eq72
       grind)
    | exact resolve eq9521 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9521
  have eq9572 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq21 eq9569
    | exact resolve eq9569 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9569
  have eq9573 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq260 X0
       have i₂ := eq66 (τ X0) (τ X0)
       grind)
    | exact superpose eq66 eq260
    | (have j0 := eq260 X0
       grind)
    | exact resolve eq260 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq260
  have eq9768 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq355 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq9573 (σ X0)
       grind)
    | exact superpose eq9573 eq355
    | (have j1 := eq9573 (σ X0)
       grind)
    | exact resolve eq355 eq9573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq9573
  have eq9775 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9768 X0
       have i₂ := eq16 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq16 eq9768
    | (have j0 := eq9768 X0
       grind)
    | exact resolve eq9768 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9768
  have eq9810 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9775 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq9775
    | (have j0 := eq9775 X0
       grind)
    | exact resolve eq9775 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9775
  have eq9831 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9810 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq9810
    | (have j0 := eq9810 X0
       grind)
    | exact resolve eq9810 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9810
  have eq10259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10259
    | exact resolve eq10259 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10259
  have eq10271 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq10260
       have r₂ := eq28
       grind)
    | exact resolve eq10260 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10260
  have eq10273 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10271
    | exact resolve eq10271 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10271
  have eq10281 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10273 eq61
    | exact resolve eq61 eq10273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10315 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10281
    | exact resolve eq10281 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10281
  have eq10418 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq559 y y
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq559
    | (have j0 := eq559 y y
       grind)
    | exact resolve eq559 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq559
  have eq10560 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq10418
  have eq10587 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10560
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10560
    | exact resolve eq10560 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10560
  have eq10679 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10587
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10587
    | exact resolve eq10587 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10587
  have eq11011 : x ≠ y ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq10315
       grind)
    | exact superpose eq10315 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10315
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10315
       grind)
    | exact resolve eq13 eq10315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18093 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq10315
       grind)
    | exact superpose eq10315 eq129
    | exact resolve eq129 eq10315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq10315
  have eq18149 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18093
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18093
    | exact resolve eq18093 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18093
  have eq18857 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18149 eq10679
    | exact resolve eq10679 eq18149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10679 eq18149
  have eq18880 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18857
    | exact resolve eq18857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18857
  have eq18881 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18880
  have eq18904 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18881 eq69
    | (have r₁ := eq69 (σ y) (σ y)
       have r₂ := eq18881
       grind)
    | (have r₁ := eq69 (σ x) (σ y)
       have r₂ := eq18881
       grind)
    | (have r₁ := eq69 x y
       have r₂ := eq18881
       grind)
    | exact resolve eq69 eq18881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq18881
  have eq18938 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18904
  have eq19063 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18938 eq128
    | exact resolve eq128 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq18938
  have eq19110 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq19063
    | exact resolve eq19063 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19063
  have eq19114 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19110
       have r₂ := eq11011
       grind)
    | exact resolve eq19110 eq11011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11011 eq19110
  have eq19134 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq564 y y
       have i₂ := eq19114
       grind)
    | exact superpose eq19114 eq564
    | (have j0 := eq564 y y
       grind)
    | exact resolve eq564 eq19114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq19114
  have eq19135 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19134
  have eq19136 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19135
  have eq19148 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19136
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19136
    | exact resolve eq19136 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19136
  have eq19629 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19148 eq65
    | exact resolve eq65 eq19148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq19148
  have eq19684 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19629 x
       have i₂ := eq61 sF3 x
       grind)
    | exact superpose eq61 eq19629
    | exact resolve eq19629 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19629
  have eq20293 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19684 eq27
    | (have j1 := eq19684 (σ x)
       grind)
    | exact resolve eq27 eq19684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19684
  have eq20305 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20293
  have eq20310 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20305 eq28
    | exact resolve eq28 eq20305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20316 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20305 eq88
    | (have r₁ := eq88
       have r₂ := eq20305
       grind)
    | exact resolve eq88 eq20305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq20335 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20305
  have eq20336 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20316
       have r₂ := eq52
       grind)
    | exact resolve eq20316 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq20316
  have eq33816 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10273 eq9831
    | exact resolve eq9831 eq10273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10273
  have eq33865 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq33816
       have r₂ := eq20335
       grind)
    | exact resolve eq33816 eq20335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33816
  have eq33874 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33865 eq122
    | exact resolve eq122 eq33865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq33865
  have eq33895 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33874
  have eq33932 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61 y y
       have i₂ := eq33895
       grind)
    | exact superpose eq33895 eq61
    | exact resolve eq61 eq33895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq33895
  have eq33994 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33932
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33932
    | exact resolve eq33932 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33932
  have eq34002 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33994 eq64
    | exact resolve eq64 eq33994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34123 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34002 eq802
    | exact resolve eq802 eq34002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34002
  have eq34206 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq64 eq34123
    | exact resolve eq34123 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34123
  have eq34213 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq34206
    | exact resolve eq34206 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34206
  have eq34269 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34213 eq33994
    | exact resolve eq33994 eq34213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33994 eq34213
  have eq34270 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq34269
  have eq34296 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34270 eq30
    | exact resolve eq30 eq34270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq34270
  have eq34553 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq34296
    | exact resolve eq34296 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34296
  have eq34555 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq34553 eq29
    | exact resolve eq29 eq34553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34553
  have eq34810 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq34555
    | exact resolve eq34555 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq34555
  have eq34811 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq34810
  have eq34812 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq34811 eq21
    | exact resolve eq21 eq34811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34811
  have eq35014 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34812
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34812
    | exact resolve eq34812 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34812
  have eq35118 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq35014 eq20310
    | (have r₁ := eq20310
       have r₂ := eq35014
       grind)
    | exact resolve eq20310 eq35014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20310
  have eq35185 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq35118
  have eq35186 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq35185
  have eq35616 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq35186 eq64
    | exact resolve eq64 eq35186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35186
  have eq36147 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq35616 eq802
    | exact resolve eq802 eq35616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq35616
  have eq36231 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq64 eq36147
    | exact resolve eq36147 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq36147
  have eq36238 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq36231
    | exact resolve eq36231 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36231
  have eq36242 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq36238 eq28
    | exact resolve eq28 eq36238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36238
  have eq36324 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq36242
       have r₂ := eq35014
       grind)
    | exact resolve eq36242 eq35014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35014 eq36242
  have eq36330 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq36324 eq63
    | exact resolve eq63 eq36324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36775 : y = (M.op (M.op (M.op x y) x) y) ∨ x = y := by
    first
    | (have i₁ := eq798 x
       have i₂ := eq36330
       grind)
    | exact superpose eq36330 eq798
    | exact resolve eq798 eq36330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq36330
  have eq36854 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq63 eq36775
    | exact resolve eq36775 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq36775
  have eq36861 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq36854
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36854
    | exact resolve eq36854 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36854
  have eq36992 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq36861 eq36324
    | exact resolve eq36324 eq36861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36324 eq36861
  have eq36993 : x = y := by grind
  clear eq36992
  have eq37065 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq36993
       grind)
    | exact superpose eq36993 eq19
    | exact resolve eq19 eq36993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq37066 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq36993
       grind)
    | exact superpose eq36993 eq25
    | exact resolve eq25 eq36993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq36993
  have eq37233 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq37066
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37066
    | exact resolve eq37066 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37066
  have eq37663 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq37233 eq27
    | exact resolve eq27 eq37233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq37771 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37233 eq20335
    | (have r₁ := eq20335
       have r₂ := eq37233
       grind)
    | exact resolve eq20335 eq37233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20335
  have eq37772 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37233 eq20336
    | (have r₁ := eq20336
       have r₂ := eq37233
       grind)
    | exact resolve eq20336 eq37233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20336
  have eq37800 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq37772
  have eq37801 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq37771
  have eq37933 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9831 x
       have i₂ := eq37065
       grind)
    | exact superpose eq37065 eq9831
    | exact resolve eq9831 eq37065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9831 eq37065
  have eq38689 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37801 eq28
    | exact resolve eq28 eq37801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37801
  have eq40352 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq9572 eq37800
    | exact resolve eq37800 eq9572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9572 eq37800
  have eq40414 : x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | (have r₁ := eq40352
       have r₂ := eq38689
       grind)
    | exact resolve eq40352 eq38689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38689 eq40352
  have eq40418 : x = (k x (M.op x y)) := by
    first
    | (have r₁ := eq40414
       have r₂ := eq72
       grind)
    | exact resolve eq40414 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq40414
  have eq40426 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq40418 eq46
    | exact resolve eq46 eq40418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq40457 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq40426
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40426
    | exact resolve eq40426 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40426
  have eq40669 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40418 eq37933
    | exact resolve eq37933 eq40418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37933 eq40418
  have eq40670 : x = (M.op x y) := by grind
  clear eq40669
  have eq40673 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq40670 eq21
    | exact resolve eq21 eq40670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq40670
  have eq40941 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40673
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40673
    | exact resolve eq40673 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq40673
  have eq41142 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40941 eq8484
    | exact resolve eq8484 eq40941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8484
  have eq41232 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq41142
       have r₂ := eq28
       grind)
    | exact resolve eq41142 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41142
  have eq41330 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq37233 eq41232
    | exact resolve eq41232 eq37233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41232
  have eq41380 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq40457 eq41330
    | exact resolve eq41330 eq40457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40457 eq41330
  have eq41410 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq41380
       have r₂ := eq40941
       grind)
    | exact resolve eq41380 eq40941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40941 eq41380
  have eq41423 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq37233 eq41410
    | exact resolve eq41410 eq37233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37233 eq41410
  have eq41426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37663 eq41423
    | exact resolve eq41423 eq37663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37663 eq41423
  have eq41427 : False := by grind
  exact eq41427

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pyy_pyx_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq88
    | exact resolve eq88 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq103 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq61 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq61
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq109 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq63
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq112 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq109
  have eq114 : (M.op x y) = (M.op (M.op x y) x) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) := by grind
  clear eq106
  have eq116 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq103 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq118 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56 eq112
    | exact resolve eq112 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq120 : x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq55 eq114
    | exact resolve eq114 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq122 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56 eq118
    | exact resolve eq118 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq124 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55 eq120
    | exact resolve eq120 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq209 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
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
  have eq232 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq254 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq541 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X0)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq859 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq60 X1 X2 X0
       grind)
    | exact superpose eq60 eq54
    | exact resolve eq54 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq116 X0 X0 x
       have i₂ := eq54 X0 x
       grind)
    | exact superpose eq54 eq116
    | exact resolve eq116 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq978 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq935 X0
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq935
    | (have j0 := eq935 X0
       grind)
    | exact resolve eq935 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq935
  have eq997 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq978 X0
       have j1 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq978 x
       have r₂ := eq13 (M.op x x) x
       grind)
    | exact resolve eq978 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq6150 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq209 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq209
    | (have j0 := eq209 x
       grind)
    | exact resolve eq209 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq6186 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6150
  have eq6194 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6186
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6186
    | exact resolve eq6186 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6186
  have eq6211 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6194
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6194 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6194
  have eq6216 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6211 eq49
    | exact resolve eq49 eq6211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6211
  have eq6426 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (k X0 y)) (σ x)) (σ X0))) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq232 eq541
    | (have j1 := eq232 X0
       grind)
    | exact resolve eq541 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq6707 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (k X0 (M.op x y))) (σ x)) (σ X0))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq254 eq541
    | (have j1 := eq254 X0
       grind)
    | exact resolve eq541 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq541
  have eq19766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq19766
    | exact resolve eq19766 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19766
  have eq19785 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq19774
       have r₂ := eq27
       grind)
    | exact resolve eq19774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19774
  have eq19787 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq19785
    | exact resolve eq19785 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19785
  have eq19978 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq19787 eq57
    | exact resolve eq57 eq19787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19787
  have eq20062 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq19978 x
       have i₂ := eq54 sF3 x
       grind)
    | exact superpose eq54 eq19978
    | exact resolve eq19978 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19978
  have eq20416 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20062 eq26
    | (have j1 := eq20062 (σ x)
       grind)
    | exact resolve eq26 eq20062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20062
  have eq20434 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20416
  have eq21691 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq57 X0 y x
       have i₂ := eq20434
       grind)
    | exact superpose eq20434 eq57
    | exact resolve eq57 eq20434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20434
  have eq21775 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq21691 x
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq21691
    | exact resolve eq21691 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21691
  have eq23682 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21775 x
       grind)
    | exact superpose eq21775 eq18
    | (have j1 := eq21775 x
       grind)
    | exact resolve eq18 eq21775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21775
  have eq23705 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23682
  have eq24008 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23705 eq56
    | exact resolve eq56 eq23705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24016 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23705 eq122
    | exact resolve eq122 eq23705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq23705
  have eq24745 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24016 eq90
    | exact resolve eq90 eq24016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq24016
  have eq24763 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq24745
  have eq26651 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq57 X0 y x
       have i₂ := eq24763
       grind)
    | exact superpose eq24763 eq57
    | exact resolve eq57 eq24763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq26653 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq60 y x X0
       have i₂ := eq24763
       grind)
    | exact superpose eq24763 eq60
    | exact resolve eq60 eq24763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26748 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq26653 X0
       have i₂ := eq54 y X0
       grind)
    | exact superpose eq54 eq26653
    | exact resolve eq26653 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26653
  have eq26749 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq26651 x
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq26651
    | exact resolve eq26651 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26651
  have eq27690 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24763
       have i₂ := eq26748 x
       grind)
    | exact superpose eq26748 eq24763
    | exact resolve eq24763 eq26748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24763 eq26748
  have eq27756 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq27690
  have eq27771 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq27756 eq29
    | exact resolve eq29 eq27756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27756
  have eq27967 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq28 eq27771
    | exact resolve eq27771 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27771
  have eq27968 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq27967
  have eq27981 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27968 eq28
    | exact resolve eq28 eq27968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27968
  have eq28183 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq27981
    | exact resolve eq27981 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27981
  have eq28202 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28183 eq20
    | exact resolve eq20 eq28183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28214 : x = (k x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28183 eq124
    | exact resolve eq124 eq28183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq28183
  have eq28309 : x = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq28214
  have eq28363 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq28202
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28202
    | exact resolve eq28202 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28202
  have eq28409 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28363 eq26
    | exact resolve eq26 eq28363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37965 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26749 x
       grind)
    | exact superpose eq26749 eq18
    | (have j1 := eq26749 x
       grind)
    | exact resolve eq18 eq26749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26749
  have eq38007 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq37965
  have eq38112 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38007 eq24008
    | exact resolve eq24008 eq38007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24008 eq38007
  have eq38184 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq38112
  have eq38543 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38184 eq6216
    | exact resolve eq6216 eq38184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6216 eq38184
  have eq38663 : x = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq38543
    | exact resolve eq38543 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38543
  have eq39494 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq38663
       grind)
    | exact superpose eq38663 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq38663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38663
  have eq39516 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq39494
  have eq39851 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq859 x
       have i₂ := eq39516
       grind)
    | exact superpose eq39516 eq859
    | exact resolve eq859 eq39516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39516
  have eq39943 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq55 eq39851
    | exact resolve eq39851 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39851
  have eq39961 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq39943
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39943
    | exact resolve eq39943 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39943
  have eq39962 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq39961
  have eq39974 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39962 eq28
    | exact resolve eq28 eq39962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq39962
  have eq40212 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq39974
    | exact resolve eq39974 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39974
  have eq40339 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq40212
  have eq609001 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ x)) (σ x))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6426 x
       have i₂ := eq28309
       grind)
    | exact superpose eq28309 eq6426
    | (have j0 := eq6426 x
       grind)
    | exact resolve eq6426 eq28309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6426 eq28309
  have eq609967 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ x)) (σ x))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq609001
       have r₂ := eq40339
       grind)
    | exact resolve eq609001 eq40339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609001
  have eq610081 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq609967
       have i₂ := eq54 (σ x) sF2
       grind)
    | exact superpose eq54 eq609967
    | exact resolve eq609967 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609967
  have eq610183 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq610081
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq610081
    | exact resolve eq610081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610081
  have eq610242 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56 eq610183
    | exact resolve eq610183 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610183
  have eq610296 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq610242
    | exact resolve eq610242 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610242
  have eq610322 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq610296
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq610296
    | exact resolve eq610296 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610296
  have eq610330 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq610322
    | exact resolve eq610322 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610322
  have eq610331 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq610330
  have eq610336 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq610331
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq610331
    | exact resolve eq610331 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610331
  have eq610342 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28363 eq610336
    | exact resolve eq610336 eq28363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28363 eq610336
  have eq610700 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq610342
  have eq610972 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq610700
       have r₂ := eq40339
       grind)
    | exact resolve eq610700 eq40339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610700
  have eq611021 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq610972
       have r₂ := eq27
       grind)
    | exact resolve eq610972 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610972
  have eq611094 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) = (M.op X0 (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq611021 eq896
    | exact resolve eq896 eq611021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq611021
  have eq611573 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq611094 x
       have i₂ := eq54 sF1 x
       grind)
    | exact superpose eq54 eq611094
    | exact resolve eq611094 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611094
  have eq614659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq611573 eq28409
    | exact resolve eq28409 eq611573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28409 eq611573
  have eq614742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq614659
  have eq614768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq614742
       have r₂ := eq40339
       grind)
    | exact resolve eq614742 eq40339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40339 eq614742
  have eq614795 : x = (M.op x y) := by
    first
    | (have r₁ := eq614768
       have r₂ := eq27
       grind)
    | exact resolve eq614768 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614768
  have eq614808 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq614795 eq20
    | exact resolve eq20 eq614795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq614811 : x = (M.op x x) := by
    first
    | exact superpose eq614795 eq55
    | exact resolve eq55 eq614795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615476 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq614808
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq614808
    | exact resolve eq614808 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614808
  have eq617452 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq615476 eq26
    | exact resolve eq26 eq615476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq618211 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq859 x
       have i₂ := eq614811
       grind)
    | exact superpose eq614811 eq859
    | exact resolve eq859 eq614811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq618678 : y = (M.op x y) := by
    first
    | exact superpose eq55 eq618211
    | exact resolve eq618211 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq618211
  have eq618748 : y = (M.op x y) := by
    first
    | (have i₁ := eq618678
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq618678
    | exact resolve eq618678 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq618678
  have eq618771 : x = y := by
    first
    | exact superpose eq614795 eq618748
    | exact resolve eq618748 eq614795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618748
  have eq618796 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq618771
       grind)
    | exact superpose eq618771 eq24
    | exact resolve eq24 eq618771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq618771
  have eq619557 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq618796
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq618796
    | exact resolve eq618796 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618796
  have eq619715 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq615476 eq619557
    | exact resolve eq619557 eq615476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619557
  have eq621360 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (k X0 (M.op x y))) (σ x)) (σ X0))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq619715 eq6707
    | (have j0 := eq6707 X0
       grind)
    | exact resolve eq6707 eq619715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6707
  have eq621361 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (k X0 (M.op x y))) (σ (M.op x y))) (σ X0))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq615476 eq621360
    | (have j0 := eq621360 X0
       grind)
    | exact resolve eq621360 eq615476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621360
  have eq621362 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (k X0 x)) (σ (M.op x y))) (σ X0))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq614795 eq621361
    | (have j0 := eq621361 X0
       grind)
    | exact resolve eq621361 eq614795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614795 eq621361
  have eq623700 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (M.op x x)) (σ (M.op x y))) (σ (M.op x x)))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq621362 (M.op x x)
       have i₂ := eq997 x
       grind)
    | exact superpose eq997 eq621362
    | (have j0 := eq621362 (M.op x x)
       grind)
    | exact resolve eq621362 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997 eq621362
  have eq624997 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x x))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq623700
       have i₂ := eq54 (σ (M.op x x)) sF1
       grind)
    | exact superpose eq54 eq623700
    | exact resolve eq623700 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623700
  have eq625452 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq624997
       have i₂ := eq614811
       grind)
    | exact superpose eq614811 eq624997
    | exact resolve eq624997 eq614811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624997
  have eq625864 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq625452
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq625452
    | exact resolve eq625452 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625452
  have eq626228 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | exact superpose eq56 eq625864
    | exact resolve eq625864 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq625864
  have eq626516 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | exact superpose eq615476 eq626228
    | exact resolve eq626228 eq615476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626228
  have eq626757 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq626516
       have i₂ := eq614811
       grind)
    | exact superpose eq614811 eq626516
    | exact resolve eq626516 eq614811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626516
  have eq626979 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq626757
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq626757
    | exact resolve eq626757 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626757
  have eq627143 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
    first
    | exact superpose eq615476 eq626979
    | exact resolve eq626979 eq615476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626979
  have eq627144 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by grind
  clear eq627143
  have eq627273 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq627144
       have i₂ := eq614811
       grind)
    | exact superpose eq614811 eq627144
    | exact resolve eq627144 eq614811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614811 eq627144
  have eq627380 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq627273
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq627273
    | exact resolve eq627273 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq627273
  have eq627449 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq615476 eq627380
    | exact resolve eq627380 eq615476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615476 eq627380
  have eq627450 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq627449
  have eq627645 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq627450 eq60
    | exact resolve eq60 eq627450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq627450
  have eq628069 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq627645 x
       have i₂ := eq54 sF1 x
       grind)
    | exact superpose eq54 eq627645
    | exact resolve eq627645 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq627645
  have eq672190 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq628069 eq617452
    | exact resolve eq617452 eq628069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617452 eq628069
  have eq672191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq619715 eq672190
    | exact resolve eq672190 eq619715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619715 eq672190
  have eq672192 : False := by grind
  exact eq672192

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pyy_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq81 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq128 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq133 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq128
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq139 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133
    | exact resolve eq133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq140 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq139
    | exact resolve eq139 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq141 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq140
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq140
    | exact resolve eq140 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq164 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq189 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq164 eq16
    | exact resolve eq16 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
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
  have eq250 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq339 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq12 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq346 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq339 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq347 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq346 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq346
    | (have j0 := eq346 X0 X1
       grind)
    | exact resolve eq346 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq781 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X1) (σ X0)
       have i₂ := eq105 X0 X1
       grind)
    | exact superpose eq105 eq54
    | (have j1 := eq105 X0 X1
       grind)
    | exact resolve eq54 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq851 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq60
    | (have j0 := eq60 (σ x) X0 (σ y)
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq927 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq94 X0 X0 x
       have i₂ := eq54 X0 x
       grind)
    | exact superpose eq54 eq94
    | exact resolve eq94 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq970 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq927 X0
       have j1 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq927 x
       have r₂ := eq13 (M.op x x) x
       grind)
    | exact resolve eq927 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq6085 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq204 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq204
    | (have j0 := eq204 x
       grind)
    | exact resolve eq204 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq6122 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6085
  have eq6132 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6122
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6122
    | exact resolve eq6122 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6122
  have eq6149 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6132
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6132 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6132
  have eq6154 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6149 eq49
    | exact resolve eq49 eq6149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6149
  have eq6628 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq250
    | (have j0 := eq250 (M.op x y)
       grind)
    | exact resolve eq250 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq6661 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6628
  have eq6667 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq164 eq6661
    | exact resolve eq6661 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq6661
  have eq6698 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6667
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6667 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6667
  have eq6747 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6698 eq189
    | exact resolve eq189 eq6698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq6698
  have eq21360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq141 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq21360
    | exact resolve eq21360 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21360
  have eq21380 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq21369
       have r₂ := eq27
       grind)
    | exact resolve eq21369 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21369
  have eq21382 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq21380
    | exact resolve eq21380 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21380
  have eq21390 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21382 eq54
    | exact resolve eq54 eq21382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21382
  have eq21443 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21390
    | exact resolve eq21390 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21390
  have eq21447 : x ≠ x ∨ x = (M.op x y) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq21443
       grind)
    | exact superpose eq21443 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq21443
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq21443
       grind)
    | exact resolve eq12 eq21443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21443
  have eq21500 : x = (M.op x y) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21447
  have eq21506 : x = (M.op x y) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21500
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21500
    | exact resolve eq21500 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21500
  have eq21507 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21506
  have eq21882 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq781 y x
       have i₂ := eq21507
       grind)
    | exact superpose eq21507 eq781
    | (have j0 := eq781 y x
       grind)
    | exact resolve eq781 eq21507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq21507
  have eq21888 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21882
  have eq21893 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21888
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21888
    | exact resolve eq21888 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21888
  have eq21907 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21893
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21893
    | exact resolve eq21893 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21893
  have eq21916 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21907
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21907
    | exact resolve eq21907 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21907
  have eq21923 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21916
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21916
    | exact resolve eq21916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21916
  have eq21930 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21923
    | exact resolve eq21923 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21923
  have eq21931 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21930
  have eq23197 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21931 eq54
    | exact resolve eq54 eq21931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21931
  have eq23254 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23197
    | exact resolve eq23197 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23197
  have eq23255 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23254
  have eq23256 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23255 eq27
    | exact resolve eq27 eq23255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23258 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23255 eq56
    | exact resolve eq56 eq23255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23286 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23255
  have eq23562 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23258 eq347
    | (have j0 := eq347 (σ x) (σ y)
       grind)
    | exact resolve eq347 eq23258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq23258
  have eq23612 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23562
       have r₂ := eq23286
       grind)
    | exact resolve eq23562 eq23286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23286 eq23562
  have eq23654 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23612 eq141
    | exact resolve eq141 eq23612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq23612
  have eq23673 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23654
  have eq23681 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23673
       have r₂ := eq23256
       grind)
    | exact resolve eq23673 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23673
  have eq23757 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq23681
       grind)
    | exact superpose eq23681 eq54
    | exact resolve eq54 eq23681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq23681
  have eq23817 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23757
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23757
    | exact resolve eq23757 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23757
  have eq23824 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23817 eq56
    | exact resolve eq56 eq23817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23817
  have eq24081 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23824 eq6154
    | exact resolve eq6154 eq23824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6154 eq23824
  have eq24183 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq24081
    | exact resolve eq24081 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24081
  have eq25865 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq24183
       grind)
    | exact superpose eq24183 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq24183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24183
  have eq25884 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq25865
  have eq25927 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq851 x
       have i₂ := eq25884
       grind)
    | exact superpose eq25884 eq851
    | exact resolve eq851 eq25884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25884
  have eq26015 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55 eq25927
    | exact resolve eq25927 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25927
  have eq26032 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26015
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26015
    | exact resolve eq26015 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26015
  have eq26033 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq26032
  have eq26040 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26033 eq20
    | exact resolve eq20 eq26033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26033
  have eq26189 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26040
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26040
    | exact resolve eq26040 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26040
  have eq26321 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26189 eq23256
    | (have r₁ := eq23256
       have r₂ := eq26189
       grind)
    | exact resolve eq23256 eq26189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23256
  have eq26335 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26321
  have eq26336 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26335
  have eq26428 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26336 eq56
    | exact resolve eq56 eq26336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26336
  have eq26808 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26428 eq855
    | exact resolve eq855 eq26428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq26428
  have eq26898 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56 eq26808
    | exact resolve eq26808 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq26808
  have eq26921 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq26898
    | exact resolve eq26898 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26898
  have eq26929 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26921 eq27
    | exact resolve eq27 eq26921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26921
  have eq26971 : x = (M.op x y) := by
    first
    | (have r₁ := eq26929
       have r₂ := eq26189
       grind)
    | exact resolve eq26929 eq26189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26189 eq26929
  have eq26976 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq26971 eq20
    | exact resolve eq20 eq26971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq26979 : x = (M.op x x) := by
    first
    | exact superpose eq26971 eq55
    | exact resolve eq55 eq26971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27125 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq26976
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26976
    | exact resolve eq26976 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26976
  have eq27174 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq27125 eq26
    | exact resolve eq26 eq27125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq27394 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq851 x
       have i₂ := eq26979
       grind)
    | exact superpose eq26979 eq851
    | exact resolve eq851 eq26979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq27396 : x = (k x x) := by
    first
    | (have i₁ := eq970 x
       have i₂ := eq26979
       grind)
    | exact superpose eq26979 eq970
    | exact resolve eq970 eq26979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq26979
  have eq27483 : y = (M.op x y) := by
    first
    | exact superpose eq55 eq27394
    | exact resolve eq27394 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq27394
  have eq27500 : y = (M.op x y) := by
    first
    | (have i₁ := eq27483
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27483
    | exact resolve eq27483 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq27483
  have eq27508 : x = y := by
    first
    | exact superpose eq26971 eq27500
    | exact resolve eq27500 eq26971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27500
  have eq27517 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq27508
       grind)
    | exact superpose eq27508 eq24
    | exact resolve eq24 eq27508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq27508
  have eq27654 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27517
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27517
    | exact resolve eq27517 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27517
  have eq27709 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27125 eq27654
    | exact resolve eq27654 eq27125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27654
  have eq28434 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27709 eq27174
    | exact resolve eq27174 eq27709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27174 eq27709
  have eq28783 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq28434 eq6747
    | exact resolve eq6747 eq28434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6747 eq28434
  have eq28866 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26971 eq28783
    | exact resolve eq28783 eq26971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26971 eq28783
  have eq28882 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq28866
       have i₂ := eq27396
       grind)
    | exact superpose eq27396 eq28866
    | exact resolve eq28866 eq27396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27396 eq28866
  have eq28929 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28882 eq15
    | exact resolve eq15 eq28882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28882
  have eq28982 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28929
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28929
    | exact resolve eq28929 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28929
  have eq28999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27125 eq28982
    | exact resolve eq28982 eq27125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27125 eq28982
  have eq29010 : False := by grind
  exact eq29010

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxy_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq100 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq102 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq104 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq108 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq43
    | exact resolve eq43 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq109 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq105 sF2
       grind)
    | exact superpose eq105 eq49
    | exact resolve eq49 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq110 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq109
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq109
    | exact resolve eq109 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq105 sF2
       grind)
    | exact superpose eq105 eq108
    | exact resolve eq108 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq108
  have eq125 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq134 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq125
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq125
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq134
    | exact resolve eq134 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq141 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq140
    | exact resolve eq140 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq142 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq141
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq141
    | exact resolve eq141 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq143 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq142
    | exact resolve eq142 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq1151 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1155 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq60
    | (have j0 := eq60 (σ x) X0 (σ y)
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq14336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq143 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14336
    | exact resolve eq14336 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14336
  have eq14354 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14343
       have r₂ := eq27
       grind)
    | exact resolve eq14343 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14343
  have eq14358 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14354
    | exact resolve eq14354 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14354
  have eq14360 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14358
    | exact resolve eq14358 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14358
  have eq14674 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14360 eq102
    | (have r₁ := eq102
       have r₂ := eq14360
       grind)
    | exact resolve eq102 eq14360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq14360
  have eq14732 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq14674
  have eq14733 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq14732
  have eq14749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14733 eq143
    | exact resolve eq143 eq14733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq14733
  have eq14763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14749
  have eq14765 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14763
       have r₂ := eq27
       grind)
    | exact resolve eq14763 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14763
  have eq15083 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq14765
       grind)
    | exact superpose eq14765 eq100
    | (have r₁ := eq100
       have r₂ := eq14765
       grind)
    | exact resolve eq100 eq14765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq15084 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq14765
       grind)
    | exact superpose eq14765 eq111
    | exact resolve eq111 eq14765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14765
  have eq15141 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15083
  have eq15142 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15141
  have eq15158 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15084
    | exact resolve eq15084 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15084
  have eq15165 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq15142
       grind)
    | exact superpose eq15142 eq125
    | exact resolve eq125 eq15142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq15142
  have eq15191 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15165
    | exact resolve eq15165 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15165
  have eq16466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15191 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq15191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15191
  have eq16476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16466
    | exact resolve eq16466 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16466
  have eq16487 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16476
       have r₂ := eq27
       grind)
    | exact resolve eq16476 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16476
  have eq16491 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16487
    | exact resolve eq16487 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16487
  have eq16493 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16491
    | exact resolve eq16491 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16491
  have eq16494 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16493
  have eq16707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16494 eq15158
    | exact resolve eq15158 eq16494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15158 eq16494
  have eq16760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16707
  have eq16772 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16760
       have r₂ := eq27
       grind)
    | exact resolve eq16760 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16760
  have eq16778 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16772 eq56
    | exact resolve eq56 eq16772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16826 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16778 eq110
    | exact resolve eq110 eq16778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq16837 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16778 eq1155
    | exact resolve eq1155 eq16778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq16778
  have eq16921 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56 eq16837
    | exact resolve eq16837 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq16837
  have eq16929 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq16826
    | exact resolve eq16826 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16826
  have eq16941 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16921
    | exact resolve eq16921 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16921
  have eq17485 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16941 eq16772
    | exact resolve eq16772 eq16941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16772 eq16941
  have eq17486 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq17485
  have eq18025 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17486 eq29
    | exact resolve eq29 eq17486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17486
  have eq18144 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq18025
    | exact resolve eq18025 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18025
  have eq20181 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1151 x
       have i₂ := eq16929
       grind)
    | exact superpose eq16929 eq1151
    | exact resolve eq1151 eq16929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16929
  have eq20267 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55 eq20181
    | exact resolve eq20181 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20181
  have eq20287 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20267
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20267
    | exact resolve eq20267 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20267
  have eq20376 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq20287
  have eq20378 : x = (M.op x y) := by
    first
    | (have r₁ := eq20376
       have r₂ := eq18144
       grind)
    | exact resolve eq20376 eq18144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18144 eq20376
  have eq20575 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20378 eq20
    | exact resolve eq20 eq20378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq20578 : x = (M.op x x) := by
    first
    | exact superpose eq20378 eq55
    | exact resolve eq55 eq20378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20718 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq20575
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20575
    | exact resolve eq20575 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20575
  have eq20735 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20718 eq26
    | exact resolve eq26 eq20718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq21179 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq20578
       grind)
    | exact superpose eq20578 eq111
    | exact resolve eq111 eq20578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq21188 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq1151 x
       have i₂ := eq20578
       grind)
    | exact superpose eq20578 eq1151
    | exact resolve eq1151 eq20578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq20578
  have eq21273 : y = (M.op x y) := by
    first
    | exact superpose eq55 eq21188
    | exact resolve eq21188 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq21188
  have eq21280 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20718 eq21179
    | exact resolve eq21179 eq20718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21179
  have eq21293 : y = (M.op x y) := by
    first
    | (have i₁ := eq21273
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21273
    | exact resolve eq21273 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq21273
  have eq21300 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq21280
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21280
    | exact resolve eq21280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21280
  have eq21308 : x = y := by
    first
    | exact superpose eq20378 eq21293
    | exact resolve eq21293 eq20378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20378 eq21293
  have eq21314 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20718 eq21300
    | exact resolve eq21300 eq20718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21300
  have eq21330 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq21308
       grind)
    | exact superpose eq21308 eq24
    | exact resolve eq24 eq21308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq21308
  have eq21450 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq21330
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21330
    | exact resolve eq21330 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21330
  have eq21504 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20718 eq21450
    | exact resolve eq21450 eq20718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20718 eq21450
  have eq22915 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21504 eq20735
    | exact resolve eq20735 eq21504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20735 eq21504
  have eq23910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21314 eq22915
    | exact resolve eq22915 eq21314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21314 eq22915
  have eq23911 : False := by grind
  exact eq23911

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxx_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq83 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq93 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq128 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq133 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq128
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq128
       grind)
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133
    | exact resolve eq133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq140 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq139
    | exact resolve eq139 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq141 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq140
    | exact resolve eq140 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq142 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq141
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq141
    | exact resolve eq141 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq868 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq60
    | (have j0 := eq60 (σ x) X0 (σ y)
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq142 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1020
    | exact resolve eq1020 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1024 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1021
       have r₂ := eq27
       grind)
    | exact resolve eq1021 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1026 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1024
    | exact resolve eq1024 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1028 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1026
    | exact resolve eq1026 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1030 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1028 eq27
    | exact resolve eq27 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1032 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1028 eq56
    | exact resolve eq56 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1028
  have eq1090 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1032 eq93
    | (have j0 := eq93 (σ x) (σ y)
       grind)
    | exact resolve eq93 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1032
  have eq1093 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1090
       have r₂ := eq1044
       grind)
    | exact resolve eq1090 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq1090
  have eq1098 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1093 eq142
    | exact resolve eq142 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1093 eq138
    | exact resolve eq138 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq1093
  have eq1102 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1098
  have eq1106 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1099
    | exact resolve eq1099 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1099
  have eq1107 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1102
       have r₂ := eq1030
       grind)
    | exact resolve eq1102 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq1102
  have eq1110 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1106
       have r₂ := eq83
       grind)
    | exact resolve eq1106 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1106
  have eq1112 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1107 eq27
    | exact resolve eq27 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1114 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1107 eq56
    | exact resolve eq56 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq1110
       grind)
    | exact superpose eq1110 eq128
    | exact resolve eq128 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq1110
  have eq1136 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1131
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1131
    | exact resolve eq1131 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq1165 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1114 eq872
    | exact resolve eq872 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1114 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1114
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1114
       grind)
    | exact resolve eq13 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1177 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1167
  have eq1183 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56 eq1165
    | exact resolve eq1165 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1186 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1183
    | exact resolve eq1183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1202 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1186 eq1107
    | exact resolve eq1107 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq1186
  have eq1203 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1202
  have eq1265 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1203 eq142
    | exact resolve eq142 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1203
  have eq1283 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1265
  have eq1489 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1136 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1490 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1489
  have eq1496 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1490
    | exact resolve eq1490 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1499 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1496
    | exact resolve eq1496 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1500 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1499
  have eq1503 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1500 eq27
    | exact resolve eq27 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq1816 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1283 eq1177
    | exact resolve eq1177 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq1283
  have eq1820 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1816
  have eq1824 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1820
       have r₂ := eq1112
       grind)
    | exact resolve eq1820 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq1820
  have eq1826 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1824 eq20
    | exact resolve eq20 eq1824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1864 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1826
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1826
    | exact resolve eq1826 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq1887 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1864 eq1503
    | (have r₁ := eq1503
       have r₂ := eq1864
       grind)
    | exact resolve eq1503 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq1892 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1887
  have eq1893 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1892
  have eq1918 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1893 eq56
    | exact resolve eq56 eq1893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq2091 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1918 eq872
    | exact resolve eq872 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq1918
  have eq2119 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56 eq2091
    | exact resolve eq2091 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq2091
  have eq2123 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2119
    | exact resolve eq2119 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119
  have eq2128 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2123 eq27
    | exact resolve eq27 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123
  have eq2157 : x = (M.op x y) := by
    first
    | (have r₁ := eq2128
       have r₂ := eq1864
       grind)
    | exact resolve eq2128 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864 eq2128
  have eq2207 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2157 eq20
    | exact resolve eq20 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2210 : x = (M.op x x) := by
    first
    | exact superpose eq2157 eq55
    | exact resolve eq55 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2246 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2207
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2207
    | exact resolve eq2207 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq2247 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2246 eq26
    | exact resolve eq26 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2297 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq868 x
       have i₂ := eq2210
       grind)
    | exact superpose eq2210 eq868
    | exact resolve eq868 eq2210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq2308 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq66 x x
       have i₂ := eq2210
       grind)
    | exact superpose eq2210 eq66
    | (have r₁ := eq66 x x
       have r₂ := eq2210
       grind)
    | exact resolve eq66 eq2210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2210
  have eq2314 : x = (k x x) := by grind
  clear eq2308
  have eq2323 : y = (M.op x y) := by
    first
    | exact superpose eq55 eq2297
    | exact resolve eq2297 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq2297
  have eq2327 : y = (M.op x y) := by
    first
    | (have i₁ := eq2323
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2323
    | exact resolve eq2323 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2323
  have eq2329 : x = y := by
    first
    | exact superpose eq2157 eq2327
    | exact resolve eq2327 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157 eq2327
  have eq2334 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2329
       grind)
    | exact superpose eq2329 eq24
    | exact resolve eq24 eq2329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2329
  have eq2367 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2334
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2334
    | exact resolve eq2334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2378 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2246 eq2367
    | exact resolve eq2367 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367
  have eq2616 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2378 eq2247
    | exact resolve eq2247 eq2378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247 eq2378
  have eq2707 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2314
       grind)
    | exact superpose eq2314 eq43
    | exact resolve eq43 eq2314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2314
  have eq2711 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2246 eq2707
    | exact resolve eq2707 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707
  have eq2712 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2711
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2711
    | exact resolve eq2711 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2711
  have eq2713 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2246 eq2712
    | exact resolve eq2712 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246 eq2712
  have eq2943 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2713 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2713
  have eq2944 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2943
  have eq2946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2616 eq2944
    | exact resolve eq2944 eq2616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2616 eq2944
  have eq2949 : False := by grind
  exact eq2949

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyy_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq83 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq93 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq128 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq133 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq128
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq128
       grind)
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133
    | exact resolve eq133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq140 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq139
    | exact resolve eq139 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq141 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq140
    | exact resolve eq140 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq142 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq141
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq141
    | exact resolve eq141 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq899 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq60
    | (have j0 := eq60 (σ x) X0 (σ y)
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq142 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1020
    | exact resolve eq1020 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1024 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1021
       have r₂ := eq27
       grind)
    | exact resolve eq1021 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1026 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1024
    | exact resolve eq1024 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1028 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1026
    | exact resolve eq1026 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1030 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1028 eq27
    | exact resolve eq27 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1032 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1028 eq56
    | exact resolve eq56 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1028
  have eq1090 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1032 eq93
    | (have j0 := eq93 (σ x) (σ y)
       grind)
    | exact resolve eq93 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1032
  have eq1093 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1090
       have r₂ := eq1044
       grind)
    | exact resolve eq1090 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq1090
  have eq1098 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1093 eq142
    | exact resolve eq142 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1093 eq138
    | exact resolve eq138 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq1093
  have eq1102 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1098
  have eq1106 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1099
    | exact resolve eq1099 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1099
  have eq1107 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1102
       have r₂ := eq1030
       grind)
    | exact resolve eq1102 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq1102
  have eq1110 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1106
       have r₂ := eq83
       grind)
    | exact resolve eq1106 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1106
  have eq1112 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1107 eq27
    | exact resolve eq27 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1114 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1107 eq56
    | exact resolve eq56 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq1110
       grind)
    | exact superpose eq1110 eq128
    | exact resolve eq128 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq1110
  have eq1136 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1131
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1131
    | exact resolve eq1131 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq1138 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1114 eq903
    | exact resolve eq903 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1114 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1114
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1114
       grind)
    | exact resolve eq13 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1150 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1140
  have eq1156 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56 eq1138
    | exact resolve eq1138 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1159 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1156
    | exact resolve eq1156 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1202 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1159 eq1107
    | exact resolve eq1107 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq1159
  have eq1203 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1202
  have eq1213 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1203 eq142
    | exact resolve eq142 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1203
  have eq1231 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1213
  have eq1489 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1136 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1490 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1489
  have eq1496 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1490
    | exact resolve eq1490 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1499 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1496
    | exact resolve eq1496 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1500 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1499
  have eq1503 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1500 eq27
    | exact resolve eq27 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq1816 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1231 eq1150
    | exact resolve eq1150 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq1231
  have eq1820 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1816
  have eq1824 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1820
       have r₂ := eq1112
       grind)
    | exact resolve eq1820 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq1820
  have eq1826 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1824 eq20
    | exact resolve eq20 eq1824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1864 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1826
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1826
    | exact resolve eq1826 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq1887 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1864 eq1503
    | (have r₁ := eq1503
       have r₂ := eq1864
       grind)
    | exact resolve eq1503 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq1892 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1887
  have eq1893 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1892
  have eq1918 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1893 eq56
    | exact resolve eq56 eq1893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq2096 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1918 eq903
    | exact resolve eq903 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq1918
  have eq2122 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56 eq2096
    | exact resolve eq2096 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq2096
  have eq2126 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2122
    | exact resolve eq2122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2131 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2126 eq27
    | exact resolve eq27 eq2126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq2160 : x = (M.op x y) := by
    first
    | (have r₁ := eq2131
       have r₂ := eq1864
       grind)
    | exact resolve eq2131 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864 eq2131
  have eq2164 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2160 eq20
    | exact resolve eq20 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2167 : x = (M.op x x) := by
    first
    | exact superpose eq2160 eq55
    | exact resolve eq55 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2203 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2164
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2164
    | exact resolve eq2164 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164
  have eq2206 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2203 eq26
    | exact resolve eq26 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2256 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq899 x
       have i₂ := eq2167
       grind)
    | exact superpose eq2167 eq899
    | exact resolve eq899 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq2258 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq2167
       grind)
    | exact superpose eq2167 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq2167
       grind)
    | exact resolve eq13 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq2272 : x = (k x x) := by grind
  clear eq2258
  have eq2280 : y = (M.op x y) := by
    first
    | exact superpose eq55 eq2256
    | exact resolve eq2256 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq2256
  have eq2284 : y = (M.op x y) := by
    first
    | (have i₁ := eq2280
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2280
    | exact resolve eq2280 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2280
  have eq2287 : x = y := by
    first
    | exact superpose eq2160 eq2284
    | exact resolve eq2284 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160 eq2284
  have eq2290 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2287
       grind)
    | exact superpose eq2287 eq24
    | exact resolve eq24 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2287
  have eq2323 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2290
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2290
    | exact resolve eq2290 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2334 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2203 eq2323
    | exact resolve eq2323 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2571 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2334 eq2206
    | exact resolve eq2206 eq2334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206 eq2334
  have eq2659 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2272
       grind)
    | exact superpose eq2272 eq43
    | exact resolve eq43 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2272
  have eq2663 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2203 eq2659
    | exact resolve eq2659 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659
  have eq2664 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2663
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2663
    | exact resolve eq2663 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2663
  have eq2665 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2203 eq2664
    | exact resolve eq2664 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203 eq2664
  have eq2797 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2665 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq2798 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2797
  have eq2800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2571 eq2798
    | exact resolve eq2798 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571 eq2798
  have eq2803 : False := by grind
  exact eq2803
