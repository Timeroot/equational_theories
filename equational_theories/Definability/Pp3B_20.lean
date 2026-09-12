import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_x_y_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq31 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq42 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : x = (τ (σ x)) := by
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
  have eq44 : y = (τ (σ y)) := by
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
  have eq55 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x X0 y
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) X0 (σ y)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq93 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = (M.op (M.op (M.op X0 X0) (M.op x y)) x) := by
    intro X0 X1
    first
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) (τ X2))) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 (k X0 (τ X1))
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq10
    | exact resolve eq10 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq148 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107
    | exact resolve eq107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq227 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq60 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X2
       have i₂ := eq227 X0 X2
       grind)
    | (have i₁ := eq9 X2 X1 X2
       have i₂ := eq227 X2 X0
       grind)
    | exact superpose eq227 eq9
    | exact resolve eq9 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X1 X1)
       have i₂ := eq227 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq9 X2 X1 (M.op X1 X1)
       have i₂ := eq227 (M.op X1 X1) X0
       grind)
    | exact superpose eq227 eq9
    | exact resolve eq9 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq148
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq148 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq294 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq73
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq296 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq294
    | exact resolve eq294 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq298 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq296
    | exact resolve eq296 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq377 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq250 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq250 eq60
    | exact resolve eq60 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq61 x
       have i₂ := eq93 X0 x
       grind)
    | exact superpose eq93 eq61
    | exact resolve eq61 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq691 : ∀ X0 X2 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) x) (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq250 X2 x y
       have i₂ := eq93 X0 x
       grind)
    | exact superpose eq93 eq250
    | exact resolve eq250 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq738 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq95 eq63
    | exact resolve eq63 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq741 : ∀ X0 X2 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) (M.op X2 X2)) := by
    intro X0 X2
    first
    | exact superpose eq95 eq250
    | exact resolve eq250 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq250
  have eq1053 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq60 X2 X3 X0
       grind)
    | exact superpose eq60 eq62
    | exact resolve eq62 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq298
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq298
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq298 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq2213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2199
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2199
    | exact resolve eq2199 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq2216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq2213
    | exact resolve eq2213 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213
  have eq2217 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq2216
       have r₂ := eq28
       grind)
    | exact resolve eq2216 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq2218 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2217
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2217
    | exact resolve eq2217 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq2254 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2218 eq741
    | exact resolve eq741 eq2218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq2218
  have eq2263 : (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq738 eq2254
    | exact resolve eq2254 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq2254
  have eq2264 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2263
  have eq2299 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq691 X0 x
       have i₂ := eq2264
       grind)
    | exact superpose eq2264 eq691
    | exact resolve eq691 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq2264
  have eq2313 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq688 eq2299
    | exact resolve eq2299 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq2299
  have eq2314 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2313
  have eq2321 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2314 eq44
    | exact resolve eq44 eq2314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2314
  have eq2335 : x = y ∨ x = y := by
    first
    | exact superpose eq43 eq2321
    | exact resolve eq2321 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2321
  have eq2336 : x = y := by grind
  clear eq2335
  have eq2340 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2336
       grind)
    | exact superpose eq2336 eq19
    | exact resolve eq19 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2341 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2336
       grind)
    | exact superpose eq2336 eq25
    | exact resolve eq25 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2336
  have eq2574 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2341
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2341
    | exact resolve eq2341 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2341
  have eq2594 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2574 eq27
    | exact resolve eq27 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2574
  have eq2785 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq2340
       grind)
    | exact superpose eq2340 eq9
    | exact resolve eq9 eq2340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2787 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 x X1
       have i₂ := eq2340
       grind)
    | exact superpose eq2340 eq60
    | exact resolve eq60 eq2340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq2790 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq227 x X0
       have i₂ := eq2340
       grind)
    | exact superpose eq2340 eq227
    | exact resolve eq227 eq2340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq2797 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 x X1
       have i₂ := eq2340
       grind)
    | exact superpose eq2340 eq254
    | exact resolve eq254 eq2340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq2801 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq377 X1 X0 x
       have i₂ := eq2340
       grind)
    | exact superpose eq2340 eq377
    | exact resolve eq377 eq2340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq2340
  have eq2817 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1053 X0 X1 X2 X3 x
       have i₂ := eq2801 x X0
       grind)
    | exact superpose eq2801 eq1053
    | exact resolve eq1053 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq2905 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq2797 x X1
       have i₂ := eq2801 x (M.op X1 sF0)
       grind)
    | exact superpose eq2801 eq2797
    | exact resolve eq2797 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797 eq2801
  have eq2916 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op x y) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq2790 X1
       grind)
    | exact superpose eq2790 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2919 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op x y) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq2790 X0
       grind)
    | exact superpose eq2790 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq2983 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2594
       have i₂ := eq2790 sF2
       grind)
    | exact superpose eq2790 eq2594
    | exact resolve eq2594 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq3058 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2817 X0 X1 X2 x
       have i₂ := eq2790 x
       grind)
    | exact superpose eq2790 eq2817
    | exact resolve eq2817 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817
  have eq3074 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq2983 eq28
    | exact resolve eq28 eq2983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2983
  have eq3159 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) X0) X2) = (M.op (M.op x y) (M.op X0 (M.op X2 (M.op x y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq3058 X0 x X2
       have i₂ := eq2790 x
       grind)
    | exact superpose eq2790 eq3058
    | exact resolve eq3058 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3058
  have eq3462 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op X1 X0) (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq3159 eq2785
    | exact resolve eq2785 eq3159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3159
  have eq3526 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op (M.op X0 X1) (M.op x y))))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq3462 eq2785
    | exact resolve eq2785 eq3462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2785 eq3462
  have eq3658 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 (M.op (M.op X0 X1) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq3526 X0 X1 (M.op X1 (M.op (M.op X0 X1) sF0))
       have i₂ := eq2790 (M.op X1 (M.op (M.op X0 X1) sF0))
       grind)
    | exact superpose eq2790 eq3526
    | exact resolve eq3526 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq3764 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq3658 eq2787
    | exact resolve eq2787 eq3658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2787 eq3658
  have eq7743 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 (M.op x y))) (τ (M.op x y))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2905 eq2919
    | (have j0 := eq2919 X0 (M.op x y)
       grind)
    | exact resolve eq2919 eq2905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8638 : ∀ X0 : G, (τ X0) = (k (k (τ (M.op x y)) (τ X0)) (τ (M.op x y))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq7743 X0
       have i₂ := eq2919 X0 sF0
       grind)
    | exact superpose eq2919 eq7743
    | (have j0 := eq7743 X0
       have j1 := eq2919 X0 (M.op x y)
       grind)
    | exact resolve eq7743 eq2919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919 eq7743
  have eq8646 : ∀ X0 : G, (τ X0) = (k (k (τ (M.op x y)) (τ X0)) (τ (M.op x y))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq8638 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8638
  have eq37458 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ (M.op x y))) X0) (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq8646 eq102
    | (have j1 := eq8646 X0
       grind)
    | exact resolve eq102 eq8646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq8646
  have eq37668 : ∀ X0 : G, (σ (τ X0)) = (k (k (M.op x y) X0) (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq37458 X0
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq37458
    | (have j0 := eq37458 X0
       grind)
    | exact resolve eq37458 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37458
  have eq37723 : ∀ X0 : G, (k (k (M.op x y) X0) (M.op x y)) = X0 ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq37668 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37668
    | (have j0 := eq37668 X0
       grind)
    | exact resolve eq37668 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37668
  have eq38284 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq37723 eq108
    | (have j1 := eq37723 (τ X0)
       grind)
    | exact resolve eq108 eq37723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37723
  have eq38315 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq38284
    | (have j0 := eq38284 X0
       grind)
    | exact resolve eq38284 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38284
  have eq38330 : ∀ X0 : G, (M.op x y) = (M.op (τ X0) (M.op x y)) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq38315 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38315
    | (have j0 := eq38315 X0
       grind)
    | exact resolve eq38315 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38315
  have eq38474 : ∀ X0 : G, (τ X0) = (M.op (M.op x y) (M.op x y)) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq38330 eq2905
    | (have j1 := eq38330 X0
       grind)
    | exact resolve eq2905 eq38330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38330
  have eq38609 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq38474 X0
       have i₂ := eq2790 sF0
       grind)
    | exact superpose eq2790 eq38474
    | (have j0 := eq38474 X0
       grind)
    | exact resolve eq38474 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790 eq38474
  have eq38610 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq38609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38609
  have eq38648 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0
       have i₂ := eq38610 X0
       grind)
    | exact superpose eq38610 eq11
    | (have j1 := eq38610 X0
       grind)
    | exact resolve eq11 eq38610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38610
  have eq38757 : ∀ X0 : G, (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq38648
    | (have j0 := eq38648 X0
       grind)
    | exact resolve eq38648 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq38648
  have eq38789 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (σ (M.op x y))) X0) (σ (σ (M.op x y)))) ∨ (τ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq38757 eq108
    | (have j1 := eq38757 (τ X0)
       grind)
    | exact resolve eq108 eq38757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq38757
  have eq38805 : ∀ X0 : G, (τ X0) = (σ (M.op x y)) ∨ (k (k (σ (σ (M.op x y))) X0) (σ (σ (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq38789 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38789
    | (have j0 := eq38789 X0
       grind)
    | exact resolve eq38789 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38789
  have eq40622 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (k (σ (σ (M.op x y))) (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq38805 sF1
       grind)
    | exact superpose eq38805 eq42
    | (have j1 := eq38805 (σ (M.op x y))
       grind)
    | exact resolve eq42 eq38805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38805
  have eq40625 : (σ (M.op x y)) = (k (k (σ (σ (M.op x y))) (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | (have r₁ := eq40622
       have r₂ := eq3074
       grind)
    | exact resolve eq40622 eq3074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40622
  have eq40638 : (σ (M.op x y)) = (k (σ (k (σ (M.op x y)) (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq31 eq40625
    | exact resolve eq40625 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq40625
  have eq40643 : (σ (M.op x y)) = (σ (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq40638
       have i₂ := eq15 (k sF1 sF0) sF1
       grind)
    | exact superpose eq15 eq40638
    | exact resolve eq40638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40638
  have eq40662 : (τ (σ (M.op x y))) = (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40643 eq10
    | exact resolve eq10 eq40643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40643
  have eq40692 : (M.op x y) = (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42 eq40662
    | exact resolve eq40662 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq40662
  have eq40732 : (M.op x y) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) ∨ (M.op x y) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq40692 eq2916
    | (have j0 := eq2916 (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2916 eq40692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916
  have eq40744 : (M.op x y) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by grind
  clear eq40732
  have eq41048 : (k (σ (M.op x y)) (M.op x y)) = (M.op (M.op x y) (M.op (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq40744 eq3764
    | exact resolve eq3764 eq40744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3764 eq40744
  have eq41081 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq41048
       have i₂ := eq2905 (M.op sF0 (M.op sF1 sF0))
       grind)
    | exact superpose eq2905 eq41048
    | exact resolve eq41048 eq2905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2905 eq41048
  have eq41082 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by grind
  clear eq41081
  have eq42014 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41082 eq40692
    | exact resolve eq40692 eq41082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40692 eq41082
  have eq42024 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq42014
  have eq42401 : False := by grind
  exact eq42401

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxy_pxx_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq55 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq81 : x ≠ (M.op x y) ∨ x = y ∨ (k y x) = (M.op y y) := by
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
  have eq82 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
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
  have eq89 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq93 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq89
  have eq94 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq100 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq16
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq379 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op X1 X1) (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq744 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (M.op X2 X2) (σ X0)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) X2 (σ X0)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq14
    | (have j1 := eq70 X0 X1
       grind)
    | exact resolve eq14 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1642
    | exact resolve eq1642 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq1646 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1643
       have r₂ := eq28
       grind)
    | exact resolve eq1643 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1648 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1646
    | exact resolve eq1646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1651 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1648 eq82
    | (have r₁ := eq82
       have r₂ := eq1648
       grind)
    | exact resolve eq82 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1648
  have eq1654 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1651
  have eq1655 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1654
  have eq1710 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1655 eq100
    | exact resolve eq100 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq1655
  have eq1717 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq128 eq1710
    | exact resolve eq1710 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq1710
  have eq1720 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1717
       have r₂ := eq81
       grind)
    | exact resolve eq1717 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq1717
  have eq1776 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1720
       grind)
    | exact superpose eq1720 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1777 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1776
  have eq1779 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1777
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1777
    | exact resolve eq1777 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1782 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1779
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1779
    | exact resolve eq1779 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1861 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 y
       have i₂ := eq1782
       grind)
    | exact superpose eq1782 eq14
    | exact resolve eq14 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq1862 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq55 eq1861
    | exact resolve eq1861 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1861
  have eq1863 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1862
  have eq1878 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1863 eq30
    | exact resolve eq30 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq1899 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1878
    | exact resolve eq1878 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq1900 : x = (M.op x y) ∨ x = y := by grind
  clear eq1899
  have eq1903 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1900 eq21
    | exact resolve eq21 eq1900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq1925 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1903
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1903
    | exact resolve eq1903 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq24199 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (σ (M.op y y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq744 y x X0
       have i₂ := eq1720
       grind)
    | exact superpose eq1720 eq744
    | (have j0 := eq744 y x x
       grind)
    | exact resolve eq744 eq1720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq1720
  have eq24381 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24199 x
       have i₂ := eq379 y x
       grind)
    | exact superpose eq379 eq24199
    | exact resolve eq24199 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq24199
  have eq24382 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24381
  have eq24461 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24382
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24382
    | exact resolve eq24382 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24382
  have eq24532 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24461
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24461
    | exact resolve eq24461 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24461
  have eq24533 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq24532
  have eq24580 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24533
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24533
    | exact resolve eq24533 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24533
  have eq24623 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24580
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24580
    | exact resolve eq24580 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24580
  have eq24662 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq24623
    | exact resolve eq24623 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24623
  have eq24688 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24662 eq28
    | exact resolve eq28 eq24662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24662
  have eq24698 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq24688
       have r₂ := eq1925
       grind)
    | exact resolve eq24688 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925 eq24688
  have eq24700 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq24698 eq30
    | exact resolve eq30 eq24698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq24698
  have eq24748 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq24700
    | exact resolve eq24700 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq24700
  have eq24749 : x = y := by grind
  clear eq24748
  have eq24752 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq24749
       grind)
    | exact superpose eq24749 eq19
    | exact resolve eq19 eq24749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq24753 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq24749
       grind)
    | exact superpose eq24749 eq25
    | exact resolve eq25 eq24749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq24749
  have eq24785 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24753
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24753
    | exact resolve eq24753 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq24753
  have eq25490 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24785 eq27
    | exact resolve eq27 eq24785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq24785
  have eq25694 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq25490 eq69
    | exact resolve eq69 eq25490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq25490
  have eq25827 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq25694
       have i₂ := eq24752
       grind)
    | exact superpose eq24752 eq25694
    | exact resolve eq25694 eq24752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24752 eq25694
  have eq26214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25827 eq15
    | exact resolve eq15 eq25827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25827
  have eq26255 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq26214
    | exact resolve eq26214 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq26214
  have eq26264 : False := by grind
  exact eq26264

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_pyx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
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
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq80 eq53
    | exact resolve eq53 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  clear eq18
  have eq97 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq59 eq97
    | exact resolve eq97 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq130 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq59
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq59
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq136 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq134
    | exact resolve eq134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq139
    | exact resolve eq139 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq171 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq218 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq28
    | exact resolve eq28 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq223 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq36
    | exact resolve eq36 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq350 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 x) x) X0
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 (M.op (M.op x x) x) x
       have r₂ := eq54 x x x
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 x) x) X0
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq366 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq59 eq366
    | exact resolve eq366 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq366
  have eq376 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq357 X0 X1 X2
       have j1 := eq350 X0 X1 X2
       grind)
    | (have r₁ := eq357 X0 X1 X2
       have r₂ := eq350 X0 X1 X2
       grind)
    | (have r₁ := eq357 X1 X1 X2
       have r₂ := eq350 X1 X1 X2
       grind)
    | exact resolve eq357 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq357
  have eq377 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq371
       have r₂ := eq104
       grind)
    | exact resolve eq371 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq1403 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq218 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq218
    | (have j0 := eq218 x
       grind)
    | exact resolve eq218 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1710 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1403 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq14 eq1403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1711 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1710
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1710
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq1710
    | exact resolve eq1710 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq2070 : ∀ X0 X1 : G, (σ (k X0 (k (M.op x y) (τ X1)))) = (k (σ X0) (k (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq171
    | (have j0 := eq171 (M.op x y) X1 X0
       grind)
    | exact resolve eq171 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq2442 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq223
    | (have j0 := eq223 (M.op x y)
       grind)
    | exact resolve eq223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq2497 : (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2442 eq14
    | (have j0 := eq14 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2498 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq2497
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2497
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2497
    | exact resolve eq2497 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497
  have eq3666 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X0 X1
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X0 X1
       grind)
    | (have r₁ := eq94 x x x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3667 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3666 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666
  have eq3676 : x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq88 eq3667
    | (have j0 := eq3667 x y
       grind)
    | exact resolve eq3667 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq3677 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq77 eq3667
    | exact resolve eq3667 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667
  have eq3695 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq3677 eq2498
    | exact resolve eq2498 eq3677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498
  have eq3696 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3677 eq2442
    | exact resolve eq2442 eq3677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442 eq3677
  have eq3698 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq3676 eq1711
    | exact resolve eq1711 eq3676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711
  have eq3699 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3676 eq1403
    | exact resolve eq1403 eq3676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403 eq3676
  have eq3703 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq3696
    | exact resolve eq3696 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696
  have eq3704 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq3695
    | exact resolve eq3695 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3695
  have eq3706 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq3699
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3699
    | exact resolve eq3699 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3699
  have eq3707 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3698
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3698
    | exact resolve eq3698 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3698
  have eq4416 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (τ (σ (M.op x y)))))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq2070 X0 sF1
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq2070
    | exact resolve eq2070 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq4537 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq37 eq4416
    | exact resolve eq4416 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4416
  have eq4577 : ∀ X0 : G, (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq4537 X0
       have i₂ := eq100 sF0
       grind)
    | exact superpose eq100 eq4537
    | exact resolve eq4537 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4537
  have eq4629 : (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (k y x) (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4577 (k y x)
       have i₂ := eq136
       grind)
    | exact superpose eq136 eq4577
    | exact resolve eq4577 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4577
  have eq4675 : (σ (M.op x y)) = (σ (k (k y x) (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3703 eq4629
    | exact resolve eq4629 eq3703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4629
  have eq5858 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq376 X0 x (M.op x x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq376
    | exact resolve eq376 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq376
  have eq75280 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3704 eq5858
    | (have r₁ := eq5858 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq3704
       grind)
    | exact resolve eq5858 eq3704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq75282 : (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq75280
  have eq75284 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3703 eq75282
    | exact resolve eq75282 eq3703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75282
  have eq75285 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq75284
  have eq75303 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq75285 eq82
    | exact resolve eq82 eq75285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75285
  have eq75370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq3707 eq75303
    | exact resolve eq75303 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75303
  have eq75382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq75370
    | exact resolve eq75370 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75370
  have eq75385 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq75382
       have r₂ := eq27
       grind)
    | exact resolve eq75382 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75382
  have eq75407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq75385 eq5858
    | (have r₁ := eq5858 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq75385
       grind)
    | exact resolve eq5858 eq75385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75385
  have eq75408 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq75407
  have eq75413 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3706 eq75408
    | exact resolve eq75408 eq3706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75408
  have eq75414 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq75413
  have eq75533 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq75414 eq39
    | exact resolve eq39 eq75414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq75414
  have eq75593 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq75533
    | exact resolve eq75533 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75533
  have eq75601 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75593 eq38
    | exact resolve eq38 eq75593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75593
  have eq75664 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq75601
    | exact resolve eq75601 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75601
  have eq75668 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75664 eq20
    | exact resolve eq20 eq75664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75669 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq75664 eq77
    | exact resolve eq77 eq75664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq75739 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq75742 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75668
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq75668
    | exact resolve eq75668 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75668
  have eq76261 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75669 (M.op y x)
       have i₂ := eq75669 x
       grind)
    | exact superpose eq75669 eq75669
    | exact resolve eq75669 eq75669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75669
  have eq76283 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq76261
  have eq76323 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq76283
       grind)
    | exact superpose eq76283 eq140
    | exact resolve eq140 eq76283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76283
  have eq76369 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76323
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq76323
    | exact resolve eq76323 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76323
  have eq76384 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75742 eq76369
    | exact resolve eq76369 eq75742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75742 eq76369
  have eq76440 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq76384
  have eq76512 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq76440 eq3703
    | exact resolve eq3703 eq76440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703 eq76440
  have eq76581 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq76512
    | exact resolve eq76512 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq76512
  have eq77077 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq75664 eq76581
    | exact resolve eq76581 eq75664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75664 eq76581
  have eq77171 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq77077
       have r₂ := eq75739
       grind)
    | exact resolve eq77077 eq75739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75739 eq77077
  have eq77175 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77171
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq77171
    | exact resolve eq77171 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77171
  have eq77178 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77175
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq77175
    | exact resolve eq77175 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77175
  have eq77180 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77178
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq77178
    | exact resolve eq77178 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq77178
  have eq77223 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq77180 eq82
    | exact resolve eq82 eq77180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq77180
  have eq82068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq3707 eq77223
    | exact resolve eq77223 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3707 eq77223
  have eq82122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq82068
    | exact resolve eq82068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82068
  have eq82123 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq82122
       have r₂ := eq27
       grind)
    | exact resolve eq82122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82122
  have eq208378 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82123 eq5858
    | (have r₁ := eq5858 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq82123
       grind)
    | exact resolve eq5858 eq82123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858 eq82123
  have eq208379 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq208378
  have eq208404 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3706 eq208379
    | exact resolve eq208379 eq3706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3706 eq208379
  have eq208405 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq208404
  have eq208430 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq208405 eq38
    | exact resolve eq38 eq208405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq208405
  have eq208520 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq208430
    | exact resolve eq208430 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq208430
  have eq208521 : x = (M.op x y) := by grind
  clear eq208520
  have eq208526 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq208521 eq20
    | exact resolve eq20 eq208521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq208535 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq208521 eq80
    | exact resolve eq80 eq208521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq208538 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq208521 eq95
    | exact resolve eq95 eq208521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq208969 : (σ (M.op x y)) = (σ (k (k y x) (M.op x x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq208521 eq4675
    | exact resolve eq4675 eq208521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675
  have eq228153 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq208521 eq208538
    | exact resolve eq208538 eq208521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208521 eq208538
  have eq228157 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq208526
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq208526
    | exact resolve eq208526 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208526
  have eq229367 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq228157 eq22
    | exact resolve eq22 eq228157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq229368 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq228157 eq26
    | exact resolve eq26 eq228157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq229376 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq228157 eq104
    | exact resolve eq104 eq228157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq229380 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq228157 eq136
    | exact resolve eq136 eq228157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq232758 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (k y x) (M.op x x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq228157 eq208969
    | exact resolve eq208969 eq228157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208969 eq228157
  have eq236305 : x = (M.op x x) := by
    first
    | (have i₁ := eq208535 (M.op x x)
       have i₂ := eq208535 x
       grind)
    | exact superpose eq208535 eq208535
    | exact resolve eq208535 eq208535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208535
  have eq236529 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq228153
       have i₂ := eq236305
       grind)
    | exact superpose eq236305 eq228153
    | (have r₁ := eq228153
       have r₂ := eq236305
       grind)
    | exact resolve eq228153 eq236305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228153
  have eq236563 : (σ (M.op x y)) = (σ (k (k y x) x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq232758
       have i₂ := eq236305
       grind)
    | exact superpose eq236305 eq232758
    | exact resolve eq232758 eq236305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232758 eq236305
  have eq236567 : x = (k y x) := by grind
  clear eq236529
  have eq236594 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq377
       have i₂ := eq236567
       grind)
    | exact superpose eq236567 eq377
    | exact resolve eq377 eq236567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq236610 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq229376
       have i₂ := eq236567
       grind)
    | exact superpose eq236567 eq229376
    | exact resolve eq229376 eq236567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229376
  have eq236611 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq229380
       have i₂ := eq236567
       grind)
    | exact superpose eq236567 eq229380
    | exact resolve eq229380 eq236567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229380
  have eq236632 : (σ (M.op x y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq236563
       have i₂ := eq236567
       grind)
    | exact superpose eq236567 eq236563
    | exact resolve eq236563 eq236567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236563 eq236567
  have eq236649 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq236632
       have i₂ := eq100 x
       grind)
    | exact superpose eq100 eq236632
    | exact resolve eq236632 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq236632
  have eq236659 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq236611
       have i₂ := eq229367
       grind)
    | exact superpose eq229367 eq236611
    | exact resolve eq236611 eq229367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236611
  have eq236660 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq236610
       have i₂ := eq229367
       grind)
    | exact superpose eq229367 eq236610
    | exact resolve eq236610 eq229367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236610
  have eq236676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq236594
       have i₂ := eq229367
       grind)
    | exact superpose eq229367 eq236594
    | exact resolve eq236594 eq229367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236594
  have eq236683 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq236649
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq236649
    | exact resolve eq236649 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq236649
  have eq236685 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq236660
       have r₂ := eq27
       grind)
    | exact resolve eq236660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236660
  have eq236687 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq236676
       have r₂ := eq27
       grind)
    | exact resolve eq236676 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236676
  have eq236690 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq236683
       have i₂ := eq229367
       grind)
    | exact superpose eq229367 eq236683
    | exact resolve eq236683 eq229367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229367 eq236683
  have eq236691 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq236690
       have r₂ := eq236685
       grind)
    | exact resolve eq236690 eq236685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236685 eq236690
  have eq236692 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq236691
       have r₂ := eq236687
       grind)
    | exact resolve eq236691 eq236687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236691
  have eq236935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq236692 eq236659
    | exact resolve eq236659 eq236692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236659
  have eq236946 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq236935
       have r₂ := eq27
       grind)
    | exact resolve eq236935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236935
  have eq237006 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq236946
       have r₂ := eq236687
       grind)
    | exact resolve eq236946 eq236687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236687 eq236946
  have eq240156 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq237006 eq229368
    | exact resolve eq229368 eq237006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229368 eq237006
  have eq243863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq236692 eq240156
    | exact resolve eq240156 eq236692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236692 eq240156
  have eq247846 : False := by grind
  exact eq247846

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq44 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X1 X3 X4 : G, (M.op X1 X3) = (M.op X1 (M.op (M.op X1 X3) X4)) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq9 (M.op X1 X3) (M.op x x) X1 X4
       have i₂ := eq9 X1 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X3 (M.op X2 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq44 X3 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq44 X2 X0 x
       grind)
    | exact superpose eq44 eq44
    | exact resolve eq44 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (τ X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X2 X0)) ≠ X0 ∨ (σ X0) = (k (σ (M.op X0 X1)) (σ (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op X0 x) (M.op x x)
       have i₂ := eq44 X0 x x
       grind)
    | exact superpose eq44 eq64
    | exact resolve eq64 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq81 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq10
    | exact resolve eq10 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq17 X0 X0
       grind)
    | exact superpose eq17 eq81
    | exact resolve eq81 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq81
  have eq84 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq23
    | exact resolve eq23 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq82 (τ X0)
       grind)
    | exact superpose eq82 eq84
    | exact resolve eq84 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq105 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (k (σ X0) (σ X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (M.op X0 X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq72
    | (have j0 := eq72 X1 (M.op X0 X0)
       grind)
    | exact resolve eq72 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq111 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X1
       have i₂ := eq82 (σ X0)
       grind)
    | exact superpose eq82 eq105
    | (have j0 := eq105 X0 X1
       grind)
    | exact resolve eq105 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq114 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op (M.op X0 X0) X1) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq44 X0 X0 X0
       grind)
    | (have i₁ := eq111 X0 X1
       have i₂ := eq44 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq44 eq111
    | (have j0 := eq111 X0 X1
       grind)
    | exact resolve eq111 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq127 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71
    | (have j0 := eq71 (σ X0) X1
       grind)
    | exact resolve eq71 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq140 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq127
    | (have j0 := eq127 X1 (σ X0)
       grind)
    | exact resolve eq127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq154 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X0) = (k (σ (M.op X0 X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1 X0
       have i₂ := eq44 X0 X0 X0
       grind)
    | exact superpose eq44 eq76
    | (have j0 := eq76 X0 X1 X0
       grind)
    | (have r₁ := eq76 x X1 x
       have r₂ := eq44 x x x
       grind)
    | exact resolve eq76 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq155 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq154 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq156 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X1)) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq155
    | exact resolve eq155 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq157 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X1)) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq156 X0 X1
       have i₂ := eq82 (σ X0)
       grind)
    | exact superpose eq82 eq156
    | exact resolve eq156 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq169 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op X0 X1))) (τ (M.op (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) (σ (M.op X0 X1))
       have i₂ := eq157 X0 X1
       grind)
    | exact superpose eq157 eq23
    | exact resolve eq23 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq172 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op X0 X1))) (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq169
    | exact resolve eq169 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq180 : ∀ X0 X1 : G, (k (τ (σ (M.op X0 X1))) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq172 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq172
    | exact resolve eq172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq183 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq180
    | exact resolve eq180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq183 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq44 X2 X0 x
       grind)
    | exact superpose eq44 eq183
    | exact resolve eq183 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq183 (M.op X0 X0) X1
       have i₂ := eq44 X0 X0 X0
       grind)
    | exact superpose eq44 eq183
    | exact resolve eq183 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X1)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq183 X0 X1
       grind)
    | exact superpose eq183 eq23
    | exact resolve eq23 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X1)) (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq194
    | exact resolve eq194 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq265 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq197 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq197
    | exact resolve eq197 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq286 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (M.op (k (σ X0) (σ X0)) X1)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq265 (M.op X0 X0) X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq265
    | exact resolve eq265 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq302 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (M.op (k (σ X0) (σ X0)) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq44 X0 X0 X0
       grind)
    | (have i₁ := eq286 X0 X1
       have i₂ := eq44 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq44 eq286
    | exact resolve eq286 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq304 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (M.op (M.op (σ X0) (σ X0)) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq302 X0 X1
       have i₂ := eq82 (σ X0)
       grind)
    | exact superpose eq82 eq302
    | exact resolve eq302 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq345 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (τ (M.op (M.op (σ X0) (σ X0)) X1))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ (M.op (M.op (σ X0) (σ X0)) X1)) X0
       have i₂ := eq304 X0 X1
       grind)
    | exact superpose eq304 eq15
    | exact resolve eq15 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq347 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (M.op (M.op (σ X0) (σ X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq11 (M.op (M.op (σ X0) (σ X0)) X1)
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq351 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq347 X0 x
       have i₂ := eq187 (σ X0) x
       grind)
    | exact superpose eq187 eq347
    | exact resolve eq347 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq347
  have eq8371 : ∀ X0 X1 : G, (τ (σ X1)) = (k (τ (σ X1)) (τ (M.op (σ X0) (σ X0)))) ∨ (M.op (M.op X0 X0) X1) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) (σ X1)
       have i₂ := eq114 X0 X1
       grind)
    | exact superpose eq114 eq23
    | (have j1 := eq114 X0 X1
       grind)
    | exact resolve eq23 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq8372 : ∀ X0 X1 : G, (τ (σ X1)) = (k (τ (σ X1)) (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op (M.op X0 X0) X1) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8371 X0 X1
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq8371
    | (have j0 := eq8371 X0 X1
       grind)
    | exact resolve eq8371 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq8371
  have eq8383 : ∀ X0 X1 : G, (τ (σ X1)) = (k (τ (σ X1)) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X1) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8372 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8372
    | (have j0 := eq8372 X0 X1
       grind)
    | exact resolve eq8372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8372
  have eq8390 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = X0 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8383 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8383
    | (have j0 := eq8383 X0 X1
       grind)
    | exact resolve eq8383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8383
  have eq8434 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X1) = X0 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X0 X1
       have i₂ := eq8390 X0 X1
       grind)
    | exact superpose eq8390 eq45
    | (have j1 := eq8390 X0 X1
       grind)
    | exact resolve eq45 eq8390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq8479 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = X0 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8390
  have eq8654 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8479 (M.op x x) X1
       have i₂ := eq44 x x x
       grind)
    | exact superpose eq44 eq8479
    | (have j0 := eq8479 X0 X1
       grind)
    | exact resolve eq8479 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8479
  have eq8674 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8434 (M.op x x) X1
       have i₂ := eq44 x x x
       grind)
    | exact superpose eq44 eq8434
    | (have j0 := eq8434 X0 X0
       grind)
    | exact resolve eq8434 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8434
  have eq8831 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 (M.op X0 X0) X0 X2
       have i₂ := eq8674 X0 X1
       grind)
    | exact superpose eq8674 eq44
    | (have j1 := eq8674 X0 X1
       grind)
    | exact resolve eq44 eq8674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8674
  have eq8931 : ∀ X1 X2 X3 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X3) ∨ (k X3 X1) = X3 ∨ (M.op X1 X2) = (M.op X1 X1) ∨ (k X2 X1) = X2 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq8831 X1 X3 (M.op X1 x)
       have i₂ := eq8831 X1 X2 x
       grind)
    | exact superpose eq8831 eq8831
    | (have j0 := eq8831 X1 X3 X2
       have j1 := eq8831 X1 X3 X2
       grind)
    | exact resolve eq8831 eq8831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8831
  have eq9135 : ∀ X1 X2 X3 : G, (k X3 X1) = X3 ∨ (M.op X1 X1) = (M.op X1 X3) ∨ (M.op X1 X2) = (M.op X1 X1) ∨ (k X2 X1) = X2 := by
    intro X1 X2 X3
    first
    | (have j0 := eq8931 X1 X3 X3
       have j1 := eq8654 X1 X3
       grind)
    | (have r₁ := eq8931 x X2 X3
       have r₂ := eq8654 x X1
       grind)
    | exact resolve eq8931 eq8654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8654 eq8931
  have eq15109 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9135 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9135
  have eq15110 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15109
  have eq15111 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq15110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15110
  have eq15390 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (τ X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq15111 X0 X1
       grind)
    | exact superpose eq15111 eq23
    | (have j1 := eq15111 (τ X0) (τ X1)
       grind)
    | exact resolve eq23 eq15111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15111
  have eq15616 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15390 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15390
    | (have j0 := eq15390 (σ X0) X1
       grind)
    | exact resolve eq15390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15390
  have eq15651 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15616 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15616
    | (have j0 := eq15616 X1 (σ X0)
       grind)
    | exact resolve eq15616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15616
  have eq16153 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15651 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq183 X0 X1
       grind)
    | exact superpose eq183 eq15651
    | (have j0 := eq15651 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq15651 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq15651
  have eq16387 : ∀ X0 X1 : G, (M.op (k (σ X0) (σ X0)) (k (σ X0) (σ X0))) = (M.op (k (σ X0) (σ X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16153 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq16153
    | (have j0 := eq16153 X0 X1
       grind)
    | exact resolve eq16153 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq16153
  have eq16478 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (M.op (M.op (σ X0) (σ X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16387 X0 X1
       have i₂ := eq82 (σ X0)
       grind)
    | exact superpose eq82 eq16387
    | (have j0 := eq16387 X0 X1
       grind)
    | exact resolve eq16387 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq16387
  have eq16551 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16478 X0 X1
       have i₂ := eq44 (σ X0) (σ X0) (σ X0)
       grind)
    | (have i₁ := eq16478 X0 X1
       have i₂ := eq44 X0 (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) x
       grind)
    | exact superpose eq44 eq16478
    | (have j0 := eq16478 X0 X1
       grind)
    | exact resolve eq16478 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16478
  have eq22157 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (M.op (σ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 (M.op (σ X0) (σ X0)) (σ (M.op X0 X1)) X2
       have i₂ := eq16551 X0 X1
       grind)
    | exact superpose eq16551 eq44
    | (have j1 := eq16551 X0 X1
       grind)
    | exact resolve eq44 eq16551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22159 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (σ (M.op X0 X1)) (M.op (σ X0) (σ X0)) x
       have i₂ := eq16551 X0 X1
       grind)
    | exact superpose eq16551 eq50
    | (have j1 := eq16551 X0 X1
       grind)
    | exact resolve eq50 eq16551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16551
  have eq22294 : ∀ X0 X2 X3 : G, (σ (M.op X2 X0)) = (M.op (M.op X3 (σ (M.op X2 X0))) (σ X0)) ∨ (M.op X2 X0) = X0 := by
    intro X0 X2 X3
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f22294_12 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
      intro X0 X1 X2
      grind
    have f22294_13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = X1 := by
      intro X0 X1 X2
      grind
    have f22294_21 : (σ (M.op X2 X0)) ≠ (M.op (M.op X3 (σ (M.op X2 X0))) (σ X0)) := by grind
    have f22294_22 : X0 ≠ (M.op X2 X0) := by grind
    have f22294_78 : ∀ X0 X1 X2 : G, (σ (M.op X1 X0)) = (M.op (M.op X2 (σ (M.op X1 X0))) (σ X0)) ∨ (M.op X1 X0) = X0 := by
      intro X0 X1 X2
      first
      | (have i₁ := f22294_12 (M.op X0 X1) (M.op X1 X2) X2
         have i₂ := f22294_13 X0 X1 X2
         grind)
      | exact superpose f22294_13 f22294_12
      | exact resolve f22294_12 f22294_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f22294_607 : (σ (M.op X2 X0)) ≠ (σ (M.op X2 X0)) ∨ X0 = (M.op X2 X0) := by
      first
      | (have i₁ := f22294_21
         have i₂ := f22294_78 X0 X2 X3
         grind)
      | exact superpose f22294_78 f22294_21
      | (have j1 := f22294_78 X0 X2 x
         grind)
      | (have r₁ := f22294_21
         have r₂ := f22294_78 X0 X2 X3
         grind)
      | exact resolve f22294_21 f22294_78
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f22294_620 : X0 = (M.op X2 X0) := by grind
    have f22294_625 : False := by
      first
      | (have r₁ := f22294_620
         have r₂ := f22294_22
         grind)
      | exact resolve f22294_620 f22294_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f22294_625
  clear eq22159
  have eq29557 : ∀ X0 X2 X3 : G, (σ X0) = (M.op (σ (M.op X2 X0)) (M.op (σ X0) X3)) ∨ (M.op X2 X0) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq22157 (M.op X0 x) (M.op x x) X2
       have i₂ := eq44 X0 x x
       grind)
    | exact superpose eq44 eq22157
    | exact resolve eq22157 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29833 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22157 X0 X1 (M.op (σ X1) x)
       have i₂ := eq29557 X1 X0 x
       grind)
    | exact superpose eq29557 eq22157
    | (have j0 := eq22157 X0 X1 x
       have j1 := eq29557 X1 X0 x
       grind)
    | exact resolve eq22157 eq29557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22157 eq29557
  have eq40551 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29833 x y
       grind)
    | exact superpose eq29833 eq16
    | (have j1 := eq29833 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq29833 x y
       grind)
    | exact resolve eq16 eq29833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29833
  have eq40803 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq40551
  have eq40983 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq44 X0 x y
       have i₂ := eq40803
       grind)
    | exact superpose eq40803 eq44
    | exact resolve eq44 eq40803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40984 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq44 x y X0
       have i₂ := eq40803
       grind)
    | exact superpose eq40803 eq44
    | exact resolve eq44 eq40803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40803
  have eq41082 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op (M.op X1 x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq50 y x x
       have i₂ := eq40983 X0
       grind)
    | exact superpose eq40983 eq50
    | (have j1 := eq40983 X0
       grind)
    | exact resolve eq50 eq40983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq40983
  have eq41168 : ∀ X1 : G, x = (M.op (M.op X1 x) y) := by
    intro X1
    first
    | (have j0 := eq41082 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41082
  have eq41203 : ∀ X1 : G, y = (M.op x (M.op y X1)) := by
    intro X1
    first
    | (have i₁ := eq44 (M.op x x) y X1
       have i₂ := eq41168 x
       grind)
    | exact superpose eq41168 eq44
    | exact resolve eq44 eq41168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41214 : x = (k y (M.op x x)) := by
    first
    | (have i₁ := eq184 y (M.op x x)
       have i₂ := eq41168 x
       grind)
    | exact superpose eq41168 eq184
    | exact resolve eq184 eq41168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq41285 : ∀ X1 : G, x = y ∨ (σ x) = (M.op (M.op X1 (σ x)) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq22294 y (M.op X1 x) x
       have i₂ := eq41168 X1
       grind)
    | exact superpose eq41168 eq22294
    | exact resolve eq22294 eq41168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22294
  have eq41723 : ∀ X0 X1 : G, y = (M.op y (M.op y X1)) ∨ x = (M.op (M.op X0 x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 x y
       have i₂ := eq40984 X1
       grind)
    | exact superpose eq40984 eq44
    | (have j1 := eq40984 X1
       grind)
    | exact resolve eq44 eq40984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40984
  have eq42437 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq41285 x
       grind)
    | exact superpose eq41285 eq16
    | (have j1 := eq41285 X0
       grind)
    | exact resolve eq16 eq41285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41285
  have eq42456 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq42437 X0
       grind)
    | (have r₁ := eq42437 X0
       have r₂ := eq351 x
       grind)
    | exact resolve eq42437 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42437
  have eq42510 : ∀ X1 : G, (σ y) = (M.op (σ x) (M.op (σ y) X1)) := by
    intro X1
    first
    | (have i₁ := eq44 (M.op x (σ x)) (σ y) X1
       have i₂ := eq42456 x
       grind)
    | exact superpose eq42456 eq44
    | exact resolve eq44 eq42456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq42456
  have eq42843 : ∀ X1 X2 : G, y = (M.op y y) ∨ x = (M.op (M.op X1 x) x) ∨ x = (M.op (M.op X2 x) x) := by
    intro X1 X2
    first
    | (have i₁ := eq41723 X1 (M.op y x)
       have i₂ := eq41723 X2 x
       grind)
    | exact superpose eq41723 eq41723
    | (have j0 := eq41723 X1 X1
       have j1 := eq41723 X1 X1
       grind)
    | exact resolve eq41723 eq41723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41723
  have eq42949 : ∀ X2 : G, x = (M.op (M.op X2 x) x) ∨ y = (M.op y y) := by
    intro X2
    first
    | (have j0 := eq42843 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42843
  have eq42953 : x = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq42949 (M.op x x)
       have i₂ := eq42949 x
       grind)
    | exact superpose eq42949 eq42949
    | exact resolve eq42949 eq42949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42987 : x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41168 (M.op x x)
       have i₂ := eq42949 x
       grind)
    | exact superpose eq42949 eq41168
    | exact resolve eq41168 eq42949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41168 eq42949
  have eq43079 : x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq42953
  have eq43086 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42987
       grind)
    | exact superpose eq42987 eq16
    | exact resolve eq16 eq42987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42987
  have eq43181 : x = (k y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41214
       have i₂ := eq43079
       grind)
    | exact superpose eq43079 eq41214
    | exact resolve eq41214 eq43079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41214
  have eq43198 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq351 x
       have i₂ := eq43079
       grind)
    | exact superpose eq43079 eq351
    | exact resolve eq351 eq43079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43079
  have eq43383 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq43181
       grind)
    | exact superpose eq43181 eq15
    | exact resolve eq15 eq43181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44351 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq43383
       grind)
    | exact superpose eq43383 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq43383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43383
  have eq44371 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq44351
       have r₂ := eq43086
       grind)
    | exact resolve eq44351 eq43086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43086 eq44351
  have eq59299 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq44371
       have i₂ := eq140 x y
       grind)
    | exact superpose eq140 eq44371
    | (have j1 := eq140 x y
       grind)
    | (have r₁ := eq44371
       have r₂ := eq140 x y
       grind)
    | exact resolve eq44371 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq59309 : y = (M.op y y) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq59299
       have r₂ := eq43198
       grind)
    | exact resolve eq59299 eq43198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43198 eq59299
  have eq59311 : y = (k y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq59309
       have r₂ := eq44371
       grind)
    | exact resolve eq59309 eq44371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44371 eq59309
  have eq59325 : x = y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq43181
       have i₂ := eq59311
       grind)
    | exact superpose eq59311 eq43181
    | exact resolve eq43181 eq59311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43181 eq59311
  have eq59339 : x = y ∨ y = (M.op y y) := by grind
  clear eq59325
  have eq59354 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59339
       grind)
    | exact superpose eq59339 eq16
    | exact resolve eq16 eq59339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59339
  have eq59488 : y = (M.op y y) := by
    first
    | (have r₁ := eq59354
       have r₂ := eq351 x
       grind)
    | exact resolve eq59354 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59354
  have eq59506 : y = (M.op x y) := by
    first
    | (have i₁ := eq41203 y
       have i₂ := eq59488
       grind)
    | exact superpose eq59488 eq41203
    | exact resolve eq41203 eq59488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41203
  have eq59531 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq351 y
       have i₂ := eq59488
       grind)
    | exact superpose eq59488 eq351
    | exact resolve eq351 eq59488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq59488
  have eq59711 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59506
       grind)
    | exact superpose eq59506 eq16
    | exact resolve eq16 eq59506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59506
  have eq60551 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq42510 (σ y)
       have i₂ := eq59531
       grind)
    | exact superpose eq59531 eq42510
    | exact resolve eq42510 eq59531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42510 eq59531
  have eq61057 : False := by grind
  exact eq61057

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(Y,Y) = X then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyy_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq25 X2 X0 x
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq25 X0 X0 X0
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq25 X0 X0 X0
       grind)
    | (have i₁ := eq86 X0 X1
       have i₂ := eq25 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq25 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | (have r₁ := eq86 x (M.op x x)
       have r₂ := eq25 x x x
       grind)
    | exact resolve eq86 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq99 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X0 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq25 X1 X1 x
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X0 X0
       have i₂ := eq14 X1 (M.op X0 X0)
       grind)
    | (have i₁ := eq25 X0 x x
       have i₂ := eq14 (M.op x x) (M.op X0 x)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X1 (M.op X0 X0)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op (M.op X0 X0) X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 X1
       have i₂ := eq25 X0 X0 X0
       grind)
    | (have i₁ := eq116 X0 X1
       have i₂ := eq25 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq25 eq116
    | (have j0 := eq116 X0 X1
       grind)
    | exact resolve eq116 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq126 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq15
    | exact resolve eq15 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq126 X0
       have i₂ := eq87 (σ X0)
       grind)
    | exact superpose eq87 eq126
    | exact resolve eq126 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq126
  have eq129 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq127 x
       grind)
    | exact superpose eq127 eq99
    | exact resolve eq99 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq182 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (M.op X0 X1) X1
       have i₂ := eq33 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq33 eq88
    | (have j0 := eq88 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq88 (M.op x X0) X0
       have r₂ := eq33 X0 (M.op x X0) x
       grind)
    | exact resolve eq88 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (M.op X0 X1)
       have i₂ := eq25 X0 X0 X1
       grind)
    | exact superpose eq25 eq88
    | (have j0 := eq88 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq88 x (M.op x x)
       have r₂ := eq25 x x x
       grind)
    | exact resolve eq88 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq185 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq186 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq182 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq201 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X1) (M.op X0 X0)
       have i₂ := eq185 X0 X1
       grind)
    | exact superpose eq185 eq15
    | exact resolve eq15 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq203 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X1)) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq201 X0 X1
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq201
    | exact resolve eq201 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq230 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ X1) (σ (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq186 X0 X1
       grind)
    | exact superpose eq186 eq15
    | exact resolve eq15 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ X1) (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 X1
       have i₂ := eq127 (M.op X0 X1)
       grind)
    | exact superpose eq127 eq230
    | exact resolve eq230 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq242 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq203 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq203
    | exact resolve eq203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq557 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq129
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq129
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq129
       have r₂ := eq14 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq129 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq557
  have eq620 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = X0 ∨ (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (σ (M.op (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 X1
       have i₂ := eq121 X0 (σ (M.op (τ X0) X1))
       grind)
    | exact superpose eq121 eq242
    | (have j1 := eq121 X0 (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq242 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq242
  have eq635 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = X0 ∨ (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq928 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = (k X0 (M.op (σ (M.op X1 (τ X0))) (σ (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231
    | exact resolve eq231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq1601 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq635 X0 X1
       grind)
    | exact superpose eq635 eq10
    | (have j1 := eq635 X0 X1
       grind)
    | exact resolve eq10 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq1853 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (σ (M.op (τ X0) X1)) X1 (M.op X0 X0)
       have i₂ := eq1601 X0 X1
       grind)
    | exact superpose eq1601 eq33
    | (have j1 := eq1601 X0 X1
       grind)
    | exact resolve eq33 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1902 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 (M.op X0 X0) X1 X2
       have i₂ := eq25 X0 X0 X0
       grind)
    | exact superpose eq25 eq104
    | (have j0 := eq104 (M.op X0 X0) X1 X2
       grind)
    | exact resolve eq104 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq2010 : ∀ X0 X1 X2 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op X0 (M.op X1 X2)) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1902 X0 X1 X2
       have i₂ := eq25 X0 X0 X0
       grind)
    | (have i₁ := eq1902 X0 X1 X2
       have i₂ := eq25 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq25 eq1902
    | (have j0 := eq1902 X0 X1 X2
       grind)
    | exact resolve eq1902 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq2471 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X2))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1853 (σ X0) X2 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1853
    | (have j0 := eq1853 (σ X0) X2 X2
       grind)
    | exact resolve eq1853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq2530 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X2))) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2471 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2471
    | (have j0 := eq2471 X0 X1 X2
       grind)
    | exact resolve eq2471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq2764 : ∀ X0 X2 X3 : G, (σ (M.op X0 X2)) = (M.op (σ X0) (M.op (σ (M.op X0 X2)) X3)) ∨ (M.op X0 X2) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq25 (M.op x (σ X0)) (σ (M.op X0 X2)) X3
       have i₂ := eq2530 X0 x X2
       grind)
    | exact superpose eq2530 eq25
    | (have j1 := eq2530 X0 x X2
       grind)
    | exact resolve eq25 eq2530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530
  have eq3035 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ X1))) = X1 ∨ (M.op (σ (M.op X0 (τ X1))) (M.op X1 X2)) = X1 ∨ (σ (M.op X0 (τ X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2010 (σ (M.op X0 (τ X1))) X1 X2
       have i₂ := eq928 X1 X0
       grind)
    | exact superpose eq928 eq2010
    | (have j0 := eq2010 (σ (M.op X0 (τ X1))) X1 X2
       grind)
    | exact resolve eq2010 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq2010
  have eq3045 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ X1))) = X1 ∨ (M.op (σ (M.op X0 (τ X1))) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3035 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq3117 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq3045 X1 X0 X2
       grind)
    | exact superpose eq3045 eq10
    | (have j1 := eq3045 X1 X0 X2
       grind)
    | exact resolve eq10 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq3212 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3117 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3117
    | (have j0 := eq3117 (σ X0) X1 X2
       grind)
    | exact resolve eq3117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3117
  have eq3326 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3212 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3212
    | (have j0 := eq3212 X0 X1 X2
       grind)
    | exact resolve eq3212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq5973 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2764 X1 X0 (M.op (σ X0) x)
       have i₂ := eq3326 X0 X1 x
       grind)
    | exact superpose eq3326 eq2764
    | (have j0 := eq2764 X1 X0 x
       have j1 := eq3326 X0 X1 x
       grind)
    | exact resolve eq2764 eq3326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764
  have eq8612 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5973 y x
       grind)
    | exact superpose eq5973 eq16
    | (have j1 := eq5973 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq5973 y x
       grind)
    | exact resolve eq16 eq5973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5973
  have eq8657 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8612
  have eq8753 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8657
       grind)
    | exact superpose eq8657 eq16
    | exact resolve eq16 eq8657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8756 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq25 X0 x y
       have i₂ := eq8657
       grind)
    | exact superpose eq8657 eq25
    | exact resolve eq25 eq8657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8757 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25 x y X0
       have i₂ := eq8657
       grind)
    | exact superpose eq8657 eq25
    | exact resolve eq25 eq8657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8657
  have eq8849 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op (M.op X1 x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq33 y X1 x
       have i₂ := eq8756 X0
       grind)
    | exact superpose eq8756 eq33
    | (have j1 := eq8756 X0
       grind)
    | exact resolve eq33 eq8756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8756
  have eq8914 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8757 (M.op y x)
       have i₂ := eq8757 x
       grind)
    | exact superpose eq8757 eq8757
    | exact resolve eq8757 eq8757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8757
  have eq8966 : x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq8914
  have eq8998 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq25 X0 x y
       have i₂ := eq8966
       grind)
    | exact superpose eq8966 eq25
    | exact resolve eq25 eq8966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8966
  have eq9220 : x = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8998 (M.op x x)
       have i₂ := eq8998 x
       grind)
    | exact superpose eq8998 eq8998
    | exact resolve eq8998 eq8998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8998
  have eq9282 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq9220
  have eq9304 : x = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq127 y
       have i₂ := eq9282
       grind)
    | exact superpose eq9282 eq127
    | exact resolve eq127 eq9282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9337 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq33 y x y
       have i₂ := eq9282
       grind)
    | exact superpose eq9282 eq33
    | exact resolve eq33 eq9282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq9282
  have eq9874 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq127 x
       have i₂ := eq9304
       grind)
    | exact superpose eq9304 eq127
    | exact resolve eq127 eq9304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10356 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have j0 := eq8849 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8849
  have eq10357 : ∀ X0 : G, x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have j0 := eq10356 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10356
  have eq10407 : x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10357 x
       have i₂ := eq9304
       grind)
    | exact superpose eq9304 eq10357
    | exact resolve eq10357 eq9304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9304
  have eq10418 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9337 (M.op x x)
       have i₂ := eq10357 x
       grind)
    | exact superpose eq10357 eq9337
    | exact resolve eq9337 eq10357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9337
  have eq10433 : x = (k y (M.op x x)) := by
    first
    | (have i₁ := eq186 (M.op x x) y
       have i₂ := eq10357 x
       grind)
    | exact superpose eq10357 eq186
    | exact resolve eq186 eq10357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq10461 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op (σ y) X1)) ∨ y = (M.op (M.op X0 x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq3326 y (M.op X0 x) X1
       have i₂ := eq10357 X0
       grind)
    | exact superpose eq10357 eq3326
    | (have j0 := eq3326 y (M.op X0 x) x
       grind)
    | exact resolve eq3326 eq10357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326
  have eq10472 : ∀ X1 : G, x = y ∨ (σ y) = (M.op (σ x) (M.op (σ y) X1)) := by
    intro X1
    first
    | (have i₁ := eq10461 x X1
       have i₂ := eq10357 x
       grind)
    | exact superpose eq10357 eq10461
    | (have j0 := eq10461 x X1
       grind)
    | exact resolve eq10461 eq10357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10357 eq10461
  have eq10657 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10418
       grind)
    | exact superpose eq10418 eq16
    | exact resolve eq16 eq10418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10418
  have eq11093 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq10472 x
       grind)
    | exact superpose eq10472 eq16
    | (have j1 := eq10472 X0
       grind)
    | exact resolve eq16 eq10472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10472
  have eq11119 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq11093 X0
       grind)
    | (have r₁ := eq11093 X0
       have r₂ := eq127 x
       grind)
    | exact resolve eq11093 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq11093
  have eq11134 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq25 X0 (σ x) (M.op (σ y) x)
       have i₂ := eq11119 x
       grind)
    | exact superpose eq11119 eq25
    | exact resolve eq25 eq11119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq11448 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10407
       grind)
    | exact superpose eq10407 eq16
    | exact resolve eq16 eq10407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10407
  have eq13879 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11134 (σ x)
       have i₂ := eq9874
       grind)
    | exact superpose eq9874 eq11134
    | exact resolve eq11134 eq9874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9874 eq11134
  have eq14005 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq13879
       have r₂ := eq11448
       grind)
    | exact resolve eq13879 eq11448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11448 eq13879
  have eq14041 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11119 (σ y)
       have i₂ := eq14005
       grind)
    | exact superpose eq14005 eq11119
    | exact resolve eq11119 eq14005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11119 eq14005
  have eq14214 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14041
       grind)
    | exact superpose eq14041 eq16
    | exact resolve eq16 eq14041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14216 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq129
       have i₂ := eq14041
       grind)
    | exact superpose eq14041 eq129
    | exact resolve eq129 eq14041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq14219 : (σ y) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8753
       have i₂ := eq14041
       grind)
    | exact superpose eq14041 eq8753
    | (have r₁ := eq8753
       have r₂ := eq14041
       grind)
    | exact resolve eq8753 eq14041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8753
  have eq14222 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10657
       have i₂ := eq14041
       grind)
    | exact superpose eq14041 eq10657
    | (have r₁ := eq10657
       have r₂ := eq14041
       grind)
    | exact resolve eq10657 eq14041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10657 eq14041
  have eq14224 : x = (M.op x x) := by grind
  clear eq14222
  have eq14225 : x = (M.op x y) := by grind
  clear eq14219
  have eq14304 : x = y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq558
       have i₂ := eq14224
       grind)
    | exact superpose eq14224 eq558
    | exact resolve eq558 eq14224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq14352 : x = (k y x) := by
    first
    | (have i₁ := eq10433
       have i₂ := eq14224
       grind)
    | exact superpose eq14224 eq10433
    | exact resolve eq10433 eq14224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10433
  have eq14472 : x = y ∨ (σ y) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14216
       have i₂ := eq14224
       grind)
    | exact superpose eq14224 eq14216
    | exact resolve eq14216 eq14224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14216 eq14224
  have eq14473 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq14214
       have i₂ := eq14225
       grind)
    | exact superpose eq14225 eq14214
    | exact resolve eq14214 eq14225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14214 eq14225
  have eq14521 : x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq14304
       have i₂ := eq14352
       grind)
    | exact superpose eq14352 eq14304
    | exact resolve eq14304 eq14352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14304
  have eq14522 : x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq14521
  have eq14524 : x = y ∨ x = y ∨ (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14472
       have i₂ := eq14352
       grind)
    | exact superpose eq14352 eq14472
    | exact resolve eq14472 eq14352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14472
  have eq14525 : x = y ∨ (σ y) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq14524
  have eq14680 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq14352
       grind)
    | exact superpose eq14352 eq15
    | exact resolve eq15 eq14352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14352
  have eq14710 : (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14522
       have i₂ := eq14680
       grind)
    | exact superpose eq14680 eq14522
    | exact resolve eq14522 eq14680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14522 eq14680
  have eq14719 : x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq14710
       have r₂ := eq14473
       grind)
    | exact resolve eq14710 eq14473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14710
  have eq14728 : x = y := by
    first
    | (have r₁ := eq14719
       have r₂ := eq14525
       grind)
    | exact resolve eq14719 eq14525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14525 eq14719
  have eq15214 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq14473
       have i₂ := eq14728
       grind)
    | exact superpose eq14728 eq14473
    | exact resolve eq14473 eq14728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14473 eq14728
  have eq15248 : False := by grind
  exact eq15248

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq54 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
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
  have eq78 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq54 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y X0
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 X0 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq78 eq54
    | exact resolve eq54 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq12
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  have eq100 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
  have eq135 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq131
    | exact resolve eq131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq101 (σ X0)
       grind)
    | exact superpose eq101 eq15
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq138 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq138
    | exact resolve eq138 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq214 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq10
    | exact resolve eq10 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 (M.op X0 X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq29
    | exact resolve eq29 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq222 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq37
    | exact resolve eq37 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq260 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq214 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq214
    | exact resolve eq214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1477 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq217 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq217
    | (have j0 := eq217 x
       grind)
    | exact resolve eq217 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1508 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1477 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq14 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1509 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1508
       have i₂ := eq54 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1508
       have i₂ := eq54 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq54 eq1508
    | exact resolve eq1508 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508
  have eq2244 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq222
    | (have j0 := eq222 (M.op x y)
       grind)
    | exact resolve eq222 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq2296 : (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2244 eq14
    | (have j0 := eq14 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2297 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2296
       have i₂ := eq54 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2296
       have i₂ := eq54 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq54 eq2296
    | exact resolve eq2296 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq5428 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X0 X1
       have i₂ := eq54 X0 X0 X0
       grind)
    | exact superpose eq54 eq95
    | (have j0 := eq95 X0 X0 X1
       grind)
    | (have r₁ := eq95 x x x
       have r₂ := eq54 x x x
       grind)
    | exact resolve eq95 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq5429 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5428 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5428
  have eq5433 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq84 eq100
    | (have r₁ := eq100 (M.op x y) y
       have r₂ := eq84 (M.op x y)
       grind)
    | exact resolve eq100 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq5434 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq81 eq100
    | (have r₁ := eq100 x (M.op x y)
       have r₂ := eq81 x
       grind)
    | exact resolve eq100 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq5440 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5434
  have eq5441 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5433
  have eq5445 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5440 eq1509
    | exact resolve eq1509 eq5440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509 eq5440
  have eq5448 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5441 eq2297
    | exact resolve eq2297 eq5441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq5449 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5441 eq2244
    | exact resolve eq2244 eq5441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244 eq5441
  have eq5451 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5445
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5445
    | exact resolve eq5445 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5445
  have eq5453 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq5449
    | exact resolve eq5449 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5449
  have eq5454 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq5448
    | exact resolve eq5448 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5448
  have eq11122 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq5451 eq54
    | exact resolve eq54 eq5451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5451
  have eq11135 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5454 eq54
    | exact resolve eq54 eq5454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq12195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11135 eq11122
    | exact resolve eq11122 eq11135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11135
  have eq12211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq12195
    | exact resolve eq12195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12195
  have eq12213 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq12211
       have r₂ := eq28
       grind)
    | exact resolve eq12211 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12211
  have eq12248 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12213 eq5429
    | exact resolve eq5429 eq12213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12213
  have eq12255 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq12248
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq12248
    | exact resolve eq12248 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12248
  have eq12932 : (τ (σ y)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12255 eq260
    | exact resolve eq260 eq12255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq12950 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq12255
  have eq12960 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq38 eq12932
    | exact resolve eq12932 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12932
  have eq12975 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq40 eq12960
    | exact resolve eq12960 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12960
  have eq13105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12975 eq5454
    | exact resolve eq5454 eq12975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5454 eq12975
  have eq13137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13105
  have eq13149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq13137
    | exact resolve eq13137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13137
  have eq13161 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13149
       have r₂ := eq28
       grind)
    | exact resolve eq13149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13149
  have eq13170 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13161 eq139
    | exact resolve eq139 eq13161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13161
  have eq13198 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq13170
    | exact resolve eq13170 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13170
  have eq13201 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13198
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13198
    | exact resolve eq13198 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13198
  have eq13250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13201 eq11122
    | exact resolve eq11122 eq13201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13277 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13250
  have eq13291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq13277
    | exact resolve eq13277 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13277
  have eq13303 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13291
       have r₂ := eq28
       grind)
    | exact resolve eq13291 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13291
  have eq13396 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13303 eq5429
    | exact resolve eq5429 eq13303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13303
  have eq13403 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13396
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq13396
    | exact resolve eq13396 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13396
  have eq13420 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13403
       have r₂ := eq12950
       grind)
    | exact resolve eq13403 eq12950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12950 eq13403
  have eq13438 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13420 eq13201
    | exact resolve eq13201 eq13420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13201
  have eq13439 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13420 eq11122
    | exact resolve eq11122 eq13420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13420
  have eq13466 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13439
  have eq13467 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13438
  have eq13493 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13467 eq27
    | exact resolve eq27 eq13467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13497 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13467 eq40
    | exact resolve eq40 eq13467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13467
  have eq13553 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq39 eq13497
    | exact resolve eq13497 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13497
  have eq13562 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq13553 eq40
    | exact resolve eq40 eq13553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13553
  have eq13609 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq13562
    | exact resolve eq13562 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13562
  have eq13617 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13609 eq39
    | exact resolve eq39 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13609
  have eq13665 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq13617
    | exact resolve eq13617 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13617
  have eq14526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13493 eq13466
    | exact resolve eq13466 eq13493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13466 eq13493
  have eq14556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14526
  have eq14573 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq14556
       have r₂ := eq28
       grind)
    | exact resolve eq14556 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14556
  have eq14584 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14573 eq40
    | exact resolve eq40 eq14573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq14573
  have eq14631 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq14584
    | exact resolve eq14584 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14584
  have eq14639 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14631 eq39
    | exact resolve eq39 eq14631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14631
  have eq14687 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq14639
    | exact resolve eq14639 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14639
  have eq14691 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14687 eq21
    | exact resolve eq21 eq14687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14692 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14687 eq78
    | exact resolve eq78 eq14687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq14718 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq14687
  have eq14719 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14691
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14691
    | exact resolve eq14691 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14691
  have eq16166 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14692 (M.op y x)
       have i₂ := eq14692 x
       grind)
    | exact superpose eq14692 eq14692
    | exact resolve eq14692 eq14692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14692
  have eq16180 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq16166
  have eq16201 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139 y
       have i₂ := eq16180
       grind)
    | exact superpose eq16180 eq139
    | exact resolve eq139 eq16180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16180
  have eq16229 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16201
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16201
    | exact resolve eq16201 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16201
  have eq16232 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14719 eq16229
    | exact resolve eq16229 eq14719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14719 eq16229
  have eq16283 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq16232
  have eq16338 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16283 eq5453
    | exact resolve eq5453 eq16283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5453
  have eq16397 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43 eq16338
    | exact resolve eq16338 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq16338
  have eq16884 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13665 eq16397
    | exact resolve eq16397 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13665 eq16397
  have eq16932 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq16884
  have eq16965 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16932
       have r₂ := eq14718
       grind)
    | exact resolve eq16932 eq14718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14718 eq16932
  have eq16968 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16965
       have i₂ := eq101 y
       grind)
    | exact superpose eq101 eq16965
    | exact resolve eq16965 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16965
  have eq16970 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16968
       have i₂ := eq139 y
       grind)
    | exact superpose eq139 eq16968
    | exact resolve eq16968 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16968
  have eq16972 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16970
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16970
    | exact resolve eq16970 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16970
  have eq17013 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16972 eq5429
    | exact resolve eq5429 eq16972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16972
  have eq17024 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17013
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq17013
    | exact resolve eq17013 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17013
  have eq17077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17024 eq11122
    | exact resolve eq11122 eq17024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11122 eq17024
  have eq17117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17077
    | exact resolve eq17077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17077
  have eq17129 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17117
       have r₂ := eq28
       grind)
    | exact resolve eq17117 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17117
  have eq35299 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17129 eq5429
    | exact resolve eq5429 eq17129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5429 eq17129
  have eq35308 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35299
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq35299
    | exact resolve eq35299 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq35299
  have eq37124 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35308 eq16283
    | exact resolve eq16283 eq35308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16283 eq35308
  have eq37190 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq37124
  have eq37221 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37190 eq39
    | exact resolve eq39 eq37190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq37190
  have eq37275 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq37221
    | exact resolve eq37221 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq37221
  have eq37276 : x = (M.op x y) := by grind
  clear eq37275
  have eq37281 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37276 eq21
    | exact resolve eq21 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq37290 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq37276 eq81
    | exact resolve eq81 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq37293 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq37276 eq96
    | exact resolve eq96 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq40764 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq37276 eq37293
    | exact resolve eq37293 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37276 eq37293
  have eq40767 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37281
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37281
    | exact resolve eq37281 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37281
  have eq41109 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq40767 eq23
    | exact resolve eq23 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq41110 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq40767 eq27
    | exact resolve eq27 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41122 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40767 eq135
    | exact resolve eq135 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq43088 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | exact superpose eq40767 eq41122
    | exact resolve eq41122 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40767 eq41122
  have eq43635 : x = (M.op x x) := by
    first
    | (have i₁ := eq37290 (M.op x x)
       have i₂ := eq37290 x
       grind)
    | exact superpose eq37290 eq37290
    | exact resolve eq37290 eq37290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37290
  have eq43783 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq40764
       have i₂ := eq43635
       grind)
    | exact superpose eq43635 eq40764
    | (have r₁ := eq40764
       have r₂ := eq43635
       grind)
    | exact resolve eq40764 eq43635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40764
  have eq43805 : x = (k y x) := by grind
  clear eq43783
  have eq43849 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43088
       have i₂ := eq43805
       grind)
    | exact superpose eq43805 eq43088
    | exact resolve eq43088 eq43805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43088 eq43805
  have eq43874 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43849
       have i₂ := eq41109
       grind)
    | exact superpose eq41109 eq43849
    | exact resolve eq43849 eq41109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43849
  have eq43875 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq43874
  have eq44056 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq139 x
       have i₂ := eq43635
       grind)
    | exact superpose eq43635 eq139
    | exact resolve eq139 eq43635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq43635
  have eq44110 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq44056
       have i₂ := eq41109
       grind)
    | exact superpose eq41109 eq44056
    | exact resolve eq44056 eq41109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41109 eq44056
  have eq44283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq44110 eq43875
    | exact resolve eq43875 eq44110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43875
  have eq44297 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq44283
       have r₂ := eq28
       grind)
    | exact resolve eq44283 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44283
  have eq45356 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq44297 eq41110
    | exact resolve eq41110 eq44297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41110 eq44297
  have eq45398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44110 eq45356
    | exact resolve eq45356 eq44110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44110 eq45356
  have eq45873 : False := by grind
  exact eq45873

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
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
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq109 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq23 X2 X0 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (σ X0) (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) (σ X0) X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
  clear eq70
  have eq685 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq195
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq195
    | (have j1 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq195 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq195
  have eq686 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq685
  have eq3832 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x y) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq24 y x x
       have i₂ := eq686
       grind)
    | exact superpose eq686 eq24
    | exact resolve eq24 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3840 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq109 x x y
       have i₂ := eq686
       grind)
    | exact superpose eq686 eq109
    | exact resolve eq109 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq43980 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3832 (M.op y x)
       have i₂ := eq23 x y x
       grind)
    | exact superpose eq23 eq3832
    | exact resolve eq3832 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3832
  have eq44409 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq175 y (σ x)
       have i₂ := eq43980
       grind)
    | exact superpose eq43980 eq175
    | exact resolve eq175 eq43980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44822 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq109 (σ y) (σ (M.op y y)) (σ x)
       have i₂ := eq44409
       grind)
    | exact superpose eq44409 eq109
    | exact resolve eq109 eq44409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq44409
  have eq44874 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44822
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq44822
    | exact resolve eq44822 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44822
  have eq45257 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (σ x) (σ y)
       have i₂ := eq44874
       grind)
    | exact superpose eq44874 eq23
    | exact resolve eq23 eq44874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44874
  have eq46411 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq45257 (σ y)
       have i₂ := eq43980
       grind)
    | exact superpose eq43980 eq45257
    | exact resolve eq45257 eq43980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43980 eq45257
  have eq46487 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq46411
  have eq46504 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46487
       have i₂ := eq174 y (σ x)
       grind)
    | exact superpose eq174 eq46487
    | exact resolve eq46487 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46487
  have eq46849 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq174 y X0
       have i₂ := eq46504
       grind)
    | exact superpose eq46504 eq174
    | exact resolve eq174 eq46504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49199 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46849 (σ y)
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq46849
    | exact resolve eq46849 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46849
  have eq50920 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49199
       have i₂ := eq46504
       grind)
    | exact superpose eq46504 eq49199
    | exact resolve eq49199 eq46504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46504 eq49199
  have eq50987 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq50920
  have eq51010 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50987
       have i₂ := eq98 (M.op x y)
       grind)
    | exact superpose eq98 eq50987
    | exact resolve eq50987 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50987
  have eq51209 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq51010
       grind)
    | exact superpose eq51010 eq10
    | exact resolve eq10 eq51010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51010
  have eq51474 : x = y ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq51209
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq51209
    | exact resolve eq51209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51209
  have eq51478 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51474
       grind)
    | exact superpose eq51474 eq16
    | exact resolve eq16 eq51474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51474
  have eq51479 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq51478
       have r₂ := eq98 x
       grind)
    | exact resolve eq51478 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51478
  have eq110061 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3840 (M.op x x)
       have i₂ := eq23 x x y
       grind)
    | exact superpose eq23 eq3840
    | exact resolve eq3840 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3840
  have eq110200 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq174 x (σ y)
       have i₂ := eq110061
       grind)
    | exact superpose eq110061 eq174
    | exact resolve eq174 eq110061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq110321 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24 (σ x) (σ y) (σ (M.op x x))
       have i₂ := eq110200
       grind)
    | exact superpose eq110200 eq24
    | exact resolve eq24 eq110200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq110200
  have eq110457 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq110321
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq110321
    | exact resolve eq110321 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110321
  have eq110533 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) (σ y) X0
       have i₂ := eq110457
       grind)
    | exact superpose eq110457 eq23
    | exact resolve eq23 eq110457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110457
  have eq110687 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq110533 (σ x)
       have i₂ := eq110061
       grind)
    | exact superpose eq110061 eq110533
    | exact resolve eq110533 eq110061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110061 eq110533
  have eq110822 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq110687
  have eq110848 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq110822
       have i₂ := eq175 x (σ y)
       grind)
    | exact superpose eq175 eq110822
    | exact resolve eq110822 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq110822
  have eq110874 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51479
       have i₂ := eq110848
       grind)
    | exact superpose eq110848 eq51479
    | exact resolve eq51479 eq110848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51479 eq110848
  have eq111030 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq110874
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq110874
       have i₂ := eq23 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq23 eq110874
    | exact resolve eq110874 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq110874
  have eq111031 : (σ x) = (σ y) := by grind
  clear eq111030
  have eq111060 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq111031
       grind)
    | exact superpose eq111031 eq10
    | exact resolve eq10 eq111031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111031
  have eq111522 : x = y := by
    first
    | (have i₁ := eq111060
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq111060
    | exact resolve eq111060 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111060
  have eq111525 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111522
       grind)
    | exact superpose eq111522 eq16
    | exact resolve eq16 eq111522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111522
  have eq111578 : False := by grind
  exact eq111578

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq61 X3 X0 x
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq350 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq351 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq352 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq347 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq347 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq347 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq368 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq352 (σ X0)
       grind)
    | exact superpose eq352 eq15
    | exact resolve eq15 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq368
    | exact resolve eq368 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq435 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq61
    | exact resolve eq61 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X1
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq61
    | exact resolve eq61 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0) x
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq62
    | exact resolve eq62 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) X1 (σ X0)
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq67
    | exact resolve eq67 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq351 (σ X0) (σ X1)
       grind)
    | exact superpose eq351 eq15
    | (have j1 := eq351 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq351 (τ X0) X1
       grind)
    | exact superpose eq351 eq17
    | (have j1 := eq351 (τ X0) X1
       grind)
    | exact resolve eq17 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq351
  have eq1076 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq490 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq490
    | exact resolve eq490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1135 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1076
    | (have j0 := eq1076 X0 X1
       grind)
    | exact resolve eq1076 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1891 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq482 x y
       grind)
    | exact superpose eq482 eq16
    | (have j1 := eq482 x y
       grind)
    | exact resolve eq16 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1936 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq482 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq2080 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1891
       have i₂ := eq1135 x y
       grind)
    | exact superpose eq1135 eq1891
    | (have j1 := eq1135 (σ x) (σ y)
       grind)
    | (have r₁ := eq1891
       have r₂ := eq1135 x y
       grind)
    | exact resolve eq1891 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2081 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2080
  have eq2086 : y ≠ y ∨ x = (M.op y x) ∨ (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2081
       grind)
    | exact superpose eq2081 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2081
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2081
       grind)
    | exact resolve eq13 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2088 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2081
       grind)
    | exact superpose eq2081 eq61
    | exact resolve eq61 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq2097 : (k x y) = (M.op y y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2086
  have eq2128 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2088 (M.op y x)
       have i₂ := eq2088 x
       grind)
    | exact superpose eq2088 eq2088
    | exact resolve eq2088 eq2088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq2146 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2128
  have eq2151 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq435 y (σ x)
       have i₂ := eq2146
       grind)
    | exact superpose eq2146 eq435
    | exact resolve eq435 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq2157 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq2146
       grind)
    | exact superpose eq2146 eq61
    | exact resolve eq61 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2362 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2157 (σ (M.op y y))
       have i₂ := eq2151
       grind)
    | exact superpose eq2151 eq2157
    | exact resolve eq2157 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151 eq2157
  have eq2383 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2362
  have eq2387 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2383
       have i₂ := eq387 y
       grind)
    | exact superpose eq387 eq2383
    | exact resolve eq2383 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2420 : ∀ X0 X1 : G, (σ y) = (σ (M.op y y)) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq69 y X1 x y
       have i₂ := eq2387
       grind)
    | exact superpose eq2387 eq69
    | exact resolve eq69 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq2749 : ∀ X0 X1 : G, (M.op y y) = (τ (σ y)) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2420 X0 X1
       grind)
    | exact superpose eq2420 eq10
    | (have j1 := eq2420 X0 X1
       grind)
    | exact resolve eq10 eq2420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420
  have eq2808 : ∀ X0 X1 : G, y = (M.op y y) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq2749 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2749
    | (have j0 := eq2749 X0 X1
       grind)
    | exact resolve eq2749 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2841 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 y) y) ∨ y = (M.op (M.op (M.op X1 X2) y) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 y X1 y
       have i₂ := eq2808 X0 X1
       grind)
    | exact superpose eq2808 eq67
    | (have j1 := eq2808 X1 X2
       grind)
    | exact resolve eq67 eq2808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2808
  have eq2903 : ∀ X0 X1 : G, y ≠ y ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have j0 := eq2841 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2841
  have eq2904 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have j0 := eq2903 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2903
  have eq2963 : y = (M.op y y) := by
    first
    | (have i₁ := eq2904 (M.op x x) y
       have i₂ := eq2904 x x
       grind)
    | exact superpose eq2904 eq2904
    | exact resolve eq2904 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2978 : ∀ X2 : G, y = (M.op y (M.op y X2)) := by
    intro X2
    first
    | (have i₁ := eq61 (M.op (M.op x x) y) y X2
       have i₂ := eq2904 x x
       grind)
    | exact superpose eq2904 eq61
    | exact resolve eq61 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq2996 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq437 y x
       have i₂ := eq2963
       grind)
    | exact superpose eq2963 eq437
    | exact resolve eq437 eq2963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq2997 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq438 y x
       have i₂ := eq2963
       grind)
    | exact superpose eq2963 eq438
    | exact resolve eq438 eq2963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq3158 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq12 (σ y) (M.op X0 (σ y))
       have i₂ := eq2997 X0
       grind)
    | exact superpose eq2997 eq12
    | (have j0 := eq12 (σ y) (M.op X0 (σ y))
       grind)
    | (have r₁ := eq12 (σ y) (M.op X0 (σ y))
       have r₂ := eq2997 X0
       grind)
    | exact resolve eq12 eq2997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3172 : ∀ X0 : G, (k (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have j0 := eq3158 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3158
  have eq3880 : ∀ X0 : G, (k y (τ (M.op X0 (σ y)))) = (τ (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq28 y (M.op X0 (σ y))
       have i₂ := eq3172 X0
       grind)
    | exact superpose eq3172 eq28
    | exact resolve eq28 eq3172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4050 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (k y (τ (M.op (M.op (σ y) X0) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3880 (M.op (σ y) X0)
       have i₂ := eq62 (σ y) X0 (σ y)
       grind)
    | exact superpose eq62 eq3880
    | exact resolve eq3880 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq41176 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1936 x y
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq1936
    | (have j0 := eq1936 x y
       grind)
    | exact resolve eq1936 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936 eq2097
  have eq41198 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq41176
  have eq41213 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41198
       have i₂ := eq2963
       grind)
    | exact superpose eq2963 eq41198
    | exact resolve eq41198 eq2963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41198
  have eq41214 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq41213
  have eq41225 : (σ x) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq436 x (σ y)
       have i₂ := eq41214
       grind)
    | exact superpose eq41214 eq436
    | exact resolve eq436 eq41214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq41250 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq41214
       grind)
    | exact superpose eq41214 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq41214
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq41214
       grind)
    | exact resolve eq12 eq41214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41252 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq41214
       grind)
    | exact superpose eq41214 eq61
    | exact resolve eq61 eq41214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41214
  have eq41287 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq41250
  have eq41295 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41287
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq41287
    | exact resolve eq41287 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41287
  have eq41356 : (k y (τ (σ x))) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3880 (σ (M.op x x))
       have i₂ := eq41225
       grind)
    | exact superpose eq41225 eq3880
    | exact resolve eq3880 eq41225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41225
  have eq41423 : x = (M.op y x) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq41356
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41356
    | exact resolve eq41356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41356
  have eq41663 : x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ (k y x))) := by
    first
    | (have i₁ := eq2996 (σ x)
       have i₂ := eq41295
       grind)
    | exact superpose eq41295 eq2996
    | exact resolve eq2996 eq41295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq41676 : (σ x) = (M.op (σ (k y x)) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41252 (σ y)
       have i₂ := eq41295
       grind)
    | exact superpose eq41295 eq41252
    | exact resolve eq41252 eq41295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41252 eq41295
  have eq41732 : x = (M.op y x) ∨ (σ x) = (M.op (σ (k y x)) (σ y)) := by grind
  clear eq41676
  have eq41786 : (σ x) = (M.op (σ (k y x)) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2978 x
       have i₂ := eq41732
       grind)
    | exact superpose eq41732 eq2978
    | exact resolve eq2978 eq41732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41823 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ (k y x)) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq41732
       grind)
    | exact superpose eq41732 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq41732
       grind)
    | exact resolve eq12 eq41732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41732
  have eq41860 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ (k y x)) (σ y)) := by grind
  clear eq41823
  have eq42136 : (k y (τ (σ x))) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3880 (σ (k y x))
       have i₂ := eq41786
       grind)
    | exact superpose eq41786 eq3880
    | exact resolve eq3880 eq41786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880 eq41786
  have eq42206 : y = (M.op y x) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq42136
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq42136
    | exact resolve eq42136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42136
  have eq42347 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ (k y x))) := by
    first
    | (have i₁ := eq2978 x
       have i₂ := eq41663
       grind)
    | exact superpose eq41663 eq2978
    | exact resolve eq2978 eq41663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978
  have eq42884 : x = y ∨ (σ y) = (M.op (σ y) (σ (k y x))) ∨ (σ y) = (M.op (σ y) (σ (k y x))) := by
    first
    | (have i₁ := eq41663
       have i₂ := eq42347
       grind)
    | exact superpose eq42347 eq41663
    | exact resolve eq41663 eq42347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41663 eq42347
  have eq42953 : (σ y) = (M.op (σ y) (σ (k y x))) ∨ x = y := by grind
  clear eq42884
  have eq43018 : ∀ X0 X1 : G, x = y ∨ (σ y) = (M.op (M.op (M.op X0 X1) (σ y)) (σ (k y x))) := by
    intro X0 X1
    first
    | (have i₁ := eq69 (σ (k y x)) X1 x (σ y)
       have i₂ := eq42953
       grind)
    | exact superpose eq42953 eq69
    | exact resolve eq69 eq42953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42953
  have eq43181 : x = y ∨ (k y x) = (τ (M.op (σ y) (σ x))) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq41423
       have i₂ := eq42206
       grind)
    | exact superpose eq42206 eq41423
    | exact resolve eq41423 eq42206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41423 eq42206
  have eq43251 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ x = y := by grind
  clear eq43181
  have eq43276 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq11 (M.op (σ y) (σ x))
       have i₂ := eq43251
       grind)
    | exact superpose eq43251 eq11
    | exact resolve eq11 eq43251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43251
  have eq43417 : ∀ X0 : G, (σ x) = (M.op (σ (k y x)) (M.op (σ x) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq61 (σ y) (σ x) X0
       have i₂ := eq43276
       grind)
    | exact superpose eq43276 eq61
    | exact resolve eq61 eq43276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43276
  have eq46208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (k y x)) (σ y)) := by
    first
    | (have i₁ := eq1891
       have i₂ := eq41860
       grind)
    | exact superpose eq41860 eq1891
    | exact resolve eq1891 eq41860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891 eq41860
  have eq46233 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (k y x)) (σ y)) := by grind
  clear eq46208
  have eq49706 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (M.op (M.op X0 X1) (σ y)) (σ (k y x))) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq43018 X0 X1
       grind)
    | exact superpose eq43018 eq16
    | (have j1 := eq43018 X0 X1
       grind)
    | exact resolve eq16 eq43018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43018
  have eq49934 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X1) (σ y)) (σ (k y x))) := by
    intro X0 X1
    first
    | (have j0 := eq49706 X0 X1
       grind)
    | (have r₁ := eq49706 X0 X1
       have r₂ := eq387 x
       grind)
    | exact resolve eq49706 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49706
  have eq50217 : ∀ X2 : G, (σ (k y x)) = (M.op (σ y) (M.op (σ (k y x)) X2)) := by
    intro X2
    first
    | (have i₁ := eq61 (M.op (M.op x x) (σ y)) (σ (k y x)) X2
       have i₂ := eq49934 x x
       grind)
    | exact superpose eq49934 eq61
    | exact resolve eq61 eq49934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq49934
  have eq50604 : (τ (σ (k y x))) = (k y (τ (M.op (σ (k y x)) (σ y)))) := by
    first
    | (have i₁ := eq4050 (M.op (σ (k y x)) x)
       have i₂ := eq50217 x
       grind)
    | exact superpose eq50217 eq4050
    | exact resolve eq4050 eq50217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4050 eq50217
  have eq50674 : (k y x) = (k y (τ (M.op (σ (k y x)) (σ y)))) := by
    first
    | (have i₁ := eq50604
       have i₂ := eq10 (k y x)
       grind)
    | exact superpose eq10 eq50604
    | exact resolve eq50604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50604
  have eq52938 : (σ x) = (M.op (σ (k y x)) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ (k y x)) (σ y)) := by
    first
    | (have i₁ := eq43417 (σ y)
       have i₂ := eq46233
       grind)
    | exact superpose eq46233 eq43417
    | exact resolve eq43417 eq46233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43417 eq46233
  have eq53008 : (σ x) = (M.op (σ (k y x)) (σ y)) ∨ x = y := by grind
  clear eq52938
  have eq53104 : ∀ X0 X1 : G, x = y ∨ (σ x) = (M.op (M.op (M.op X0 X1) (σ x)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 (σ y) X1 x (σ (k y x))
       have i₂ := eq53008
       grind)
    | exact superpose eq53008 eq69
    | exact resolve eq69 eq53008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq53008
  have eq53816 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (M.op X0 X1) (σ x)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq53104 X0 X1
       grind)
    | exact superpose eq53104 eq16
    | (have j1 := eq53104 X0 X1
       grind)
    | exact resolve eq16 eq53104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53104
  have eq54067 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (σ x)) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq53816 X0 X1
       grind)
    | (have r₁ := eq53816 X0 X1
       have r₂ := eq387 x
       grind)
    | exact resolve eq53816 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53816
  have eq54341 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2997 (M.op (M.op x x) (σ x))
       have i₂ := eq54067 x x
       grind)
    | exact superpose eq54067 eq2997
    | exact resolve eq2997 eq54067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997
  have eq54342 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3172 (M.op (M.op x x) (σ x))
       have i₂ := eq54067 x x
       grind)
    | exact superpose eq54067 eq3172
    | exact resolve eq3172 eq54067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3172 eq54067
  have eq54411 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq54342
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq54342
    | exact resolve eq54342 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54342
  have eq54429 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54341
       grind)
    | exact superpose eq54341 eq16
    | exact resolve eq16 eq54341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54463 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq54341
       grind)
    | exact superpose eq54341 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq54341
       grind)
    | exact resolve eq13 eq54341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54500 : (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq54463
  have eq54508 : (σ x) = (σ (k y x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq54500
       have i₂ := eq54411
       grind)
    | exact superpose eq54411 eq54500
    | exact resolve eq54500 eq54411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54411 eq54500
  have eq54523 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq54508
       have i₂ := eq387 y
       grind)
    | exact superpose eq387 eq54508
    | exact resolve eq54508 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54508
  have eq54528 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq54523
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq54523
    | exact resolve eq54523 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54523
  have eq54532 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq54528
       have i₂ := eq2963
       grind)
    | exact superpose eq2963 eq54528
    | exact resolve eq54528 eq2963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54528
  have eq56534 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1135 x y
       have i₂ := eq54532
       grind)
    | exact superpose eq54532 eq1135
    | (have j0 := eq1135 x y
       grind)
    | exact resolve eq1135 eq54532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135 eq54532
  have eq56643 : y = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq56534
       have r₂ := eq54429
       grind)
    | exact resolve eq56534 eq54429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56534
  have eq56751 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq54429
       have i₂ := eq56643
       grind)
    | exact superpose eq56643 eq54429
    | exact resolve eq54429 eq56643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54429 eq56643
  have eq56811 : (σ x) = (σ (k y x)) := by grind
  clear eq56751
  have eq56871 : (k y x) = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq50674
       have i₂ := eq56811
       grind)
    | exact superpose eq56811 eq50674
    | exact resolve eq50674 eq56811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50674
  have eq56889 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq56811
       grind)
    | exact superpose eq56811 eq10
    | exact resolve eq10 eq56811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56811
  have eq56986 : x = (k y x) := by
    first
    | (have i₁ := eq56889
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq56889
    | exact resolve eq56889 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56889
  have eq56990 : (k y x) = (k y (τ (σ y))) := by
    first
    | (have i₁ := eq56871
       have i₂ := eq54341
       grind)
    | exact superpose eq54341 eq56871
    | exact resolve eq56871 eq54341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54341 eq56871
  have eq57001 : (k y x) = (k y y) := by
    first
    | (have i₁ := eq56990
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq56990
    | exact resolve eq56990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56990
  have eq57006 : (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq57001
       have i₂ := eq352 y
       grind)
    | exact superpose eq352 eq57001
    | exact resolve eq57001 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq57001
  have eq57008 : y = (k y x) := by
    first
    | (have i₁ := eq57006
       have i₂ := eq2963
       grind)
    | exact superpose eq2963 eq57006
    | exact resolve eq57006 eq2963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963 eq57006
  have eq57010 : x = y := by
    first
    | (have i₁ := eq57008
       have i₂ := eq56986
       grind)
    | exact superpose eq56986 eq57008
    | exact resolve eq57008 eq56986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56986 eq57008
  have eq57013 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57010
       grind)
    | exact superpose eq57010 eq16
    | exact resolve eq16 eq57010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57010
  have eq57355 : False := by grind
  exact eq57355
